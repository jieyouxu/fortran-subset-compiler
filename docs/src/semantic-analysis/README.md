# Semantic Analysis and the High-Level Intermediate Representation (HIR)

We perform simple name resolution and type checking on the AST and lower it into an intermediate
representation called the High-Level Intermediate Representation (HIR). The HIR is like the AST,
but each node has its type and names resolved where applicable, and some constructs are lowered
into more specific representations (e.g. `CallOrIndex` in the AST is lowered into `Call` or
`Index` nodes in the HIR after we have type information on the target).

## Implementation Details

### Backing Storage

To avoid complex cyclic lifetimes and borrow checking pain, we simply allocate `Decl`s and `Type`s
in suitable arenas (on `TyCtxt`). Where `Type`s and `Decl`s need to be referenced, their unique
IDs are used instead.

### Symbol Table Organization and its Link with the Typed AST

Since we resolve all uses of names in the AST into their respective `Decl`s and `Type`s, we do not
need a separate symbol table. Instead, a simple stack of symbol tables is maintained while lowering
the AST (i.e. when building the HIR).
