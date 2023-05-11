# Lexing and Parsing

Our lexer converts the input string into a list of tokens. Each token has an associated span which
describes the character range corresponding to that token.

The list of tokens are then fed to the parser. The parser consumes tokens and gradually builds up
an Abstract Syntax Tree (AST).
