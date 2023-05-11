#![feature(let_chains)]
#![feature(map_try_insert)]

mod ast;
mod lex;
mod parse;
mod session;
mod span;
mod typeck;
mod types;

use lex::lex;

use clap::Parser as ClapParser;
use std::io::BufRead;
use string_interner::StringInterner;
use tracing::trace;

use crate::parse::Parser;
use crate::session::Session;
use crate::typeck::LowerAst;
use crate::types::TyCtxt;

#[derive(ClapParser)]
#[command(author, version, about)]
struct Args {
    input_file: Option<String>,

    #[arg(short, long, value_name = "FILE")]
    output_file: Option<String>,
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    use tracing_subscriber::prelude::*;
    use tracing_subscriber::{fmt, EnvFilter};

    let fmt_layer = fmt::layer()
        .compact()
        .with_level(true)
        .with_target(true)
        .without_time();
    let filter_layer = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new("info"))
        .unwrap();
    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let cli = Args::parse();

    let input = match cli.input_file.as_deref() {
        Some(path) => std::fs::read_to_string(path)?,
        None => {
            let mut buf = String::new();
            let stdin = std::io::stdin();
            let mut lines = stdin.lock().lines();
            while let Some(line) = lines.next() {
                buf.push_str(&line?);
                buf.push_str("\n");
            }
            buf
        }
    };

    let output_path = cli.output_file.as_deref().unwrap_or("a.out");

    use codespan_reporting::diagnostic::{Diagnostic, Label};
    use codespan_reporting::files::SimpleFiles;
    use codespan_reporting::term;
    use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

    let mut files = SimpleFiles::new();
    let file_id = files.add("input", &input);

    let writer = StandardStream::stderr(ColorChoice::Always);
    let diagnostic_config = codespan_reporting::term::Config::default();

    let mut string_interner = StringInterner::default();

    let tokens = match lex(&mut string_interner, &input) {
        Ok(tokens) => tokens,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_message(format!("unexpected token `{}`", e.source))
                .with_labels(vec![Label::primary(file_id, e.span.lo..e.span.hi)]);
            term::emit(&mut writer.lock(), &diagnostic_config, &files, &diagnostic)?;
            std::process::exit(1);
        }
    };

    trace!(?input);
    trace!(?output_path);
    trace!(?tokens);

    let ast = match Parser::new(tokens).parse_program() {
        Ok(ast) => ast,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_message(format!("parser error: {:?}", e))
                .with_labels(vec![Label::primary(file_id, e.span.lo..e.span.hi)]);
            term::emit(&mut writer.lock(), &diagnostic_config, &files, &diagnostic)?;
            std::process::exit(1);
        }
    };

    trace!("AST:\n{:#?}", ast);

    let mut tcx = TyCtxt::new_with_builtin_types_and_functions(&mut string_interner);
    let mut sess = Session::new();
    let mut type_checker = LowerAst {
        tcx: &mut tcx,
        sess: &mut sess,
    };
    let hir = match type_checker.lower_program(&ast) {
        Ok(hir) => hir,
        Err(_) => {
            for diag in sess.diagnostics {
                let diagnostic = Diagnostic::error()
                    .with_message(format!("typeck error: {:?}", diag))
                    .with_labels(vec![Label::primary(file_id, diag.span.lo..diag.span.hi)]);
                term::emit(&mut writer.lock(), &diagnostic_config, &files, &diagnostic)?;
            }
            std::process::exit(1);
        }
    };

    trace!("HIR:\n{:#?}", hir);

    Ok(())
}
