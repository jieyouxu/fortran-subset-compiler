# Semantic Analysis

We perform simple name resolution and type checking on the AST and produce an annotated AST called
the Typed AST (TAST).

Compared to the AST, the TAST has:

- Symbols are resolved and are replaced by references to Symbol Table entries.
- Symbol Tables are constructed and each new scope in the TAST is linked with a Symbol Table.
- Types are resolved and checked. TAST nodes have an associated type.

## Implementation Details

### Backing Storage

### Type Representation

**TODO**

### Symbol Table Organization and its Link with the Typed AST

**TODO**
