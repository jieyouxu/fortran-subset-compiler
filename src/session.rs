use crate::span::Span;
use crate::types::TypeId;

#[derive(Debug)]
pub struct Session {
    pub diagnostics: Vec<Diagnostic>,
}

impl Session {
    pub fn new() -> Self {
        Self {
            diagnostics: vec![],
        }
    }

    pub fn emit_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }
}

#[derive(Debug)]
pub struct Diagnostic {
    pub kind: DiagnosticKind,
    pub message: String,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub enum DiagnosticKind {
    DuplicateProcedureDeclaration,
    ParameterTypeUnspecified,
    UndeclaredVariable,
    DuplicateParameterDeclaration,
    DuplicateParameterName,
    DuplicateVariableDeclaration,
    UnexpectedType { expected: TypeId, found: TypeId },
    UsingArrayNameAsValue,
    UsingProcedureNameAsValue,
    CallOrIndexIntoPrimitiveType,
    NonIntegerBoundExpr,
    ParamArgCountMismatch { found: usize, expected: usize },
    ArgumentTypeMismatch { expected: TypeId, found: TypeId },
    ArrayIndexDimensionMismatch { expected: usize, found: usize },
    NonIntegerIndexExpr,
    InvalidBinOpExprType { found: TypeId },
    NotAssignable,
}
