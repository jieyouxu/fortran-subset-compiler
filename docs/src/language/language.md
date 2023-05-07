# [WIP] The Source Language

Our compiler only accepts a small subset of Fortran, its BNF grammar is listed here.

```ebnf
program ::= items
items ::= item items | epsilon
item ::= subroutine | procedure

subroutine ::= "SUBROUTINE" ident "(" formal_param_seq ")" stmt_seq "END"
procedure ::= ident "FUNCTION" ident "(" formal_param_seq ")" stmt_seq "END"
formal_param_seq ::= formal_params | empty
formal_params ::= formal_param "," formal_params | formal_param

stmt_seq ::= stmt stmt_seq | stmt | epsilon
stmt ::= var_decls | do_stmt | assign | if_stmt

var_decls ::= "INTEGER" var_names | "DOUBLE PRECISION" var_names
var_names ::= var_name | var_name "," var_names
var_name ::= ident | ident "(" ident_seq ")"
ident_seq ::= ident | ident "," ident_seq

do_stmt ::= "DO" ident "=" expr "," expr stmt_seq "ENDDO"

assign ::= expr "=" expr

if_stmt ::= "IF" "(" expr ")" "THEN" stmt_seq "ENDIF"
        |   "IF" "(" expr ")" "THEN" stmt_seq elseif_stmts "ELSE" stmt_seq "ENDIF"

elseif_stmts ::= "ELSIF"  "(" expr ")" "THEN" stmt_seq

expr ::= simple_expr
     |   simple_expr ("=" | "!=" | "<" | "<=" | ".GT." | ">=") simple_expr
simple_expr ::= ["+"|"-"] term {("+"|"-"|".OR.") term}
term ::= factor {("*"|"/"|"%"|".AND.") factor}
factor ::= ident_selector | number | "(" expr ")"
ident_selector ::= ident | ident "(" expr_seq ")"
expr_seq ::= expr | expr "," expr_seq

ident ::= [a-zA-Z][a-zA-Z0-9]*
```

This subset of Fortran is just enough to capture the following running code samples from the
BaOC book.

## Running Code Samples from the BaOC Book

### Figure 1.1 Finding Largest Element in a Column

```fortran
SUBROUTINE MAXCOL(A, N, LARGE, VALUE)
    DOUBLE PRECISION VALUE(N), A(N, N)
    INTEGER N, LARGE(N)
    INTEGER I, J
    DO I = 1, N
        LARGE(I) = 1
        VALUE(I) = DABS(A(1, I))
        DO J = 2, N
            IF (DABS(A(J, I).GT.VALUE(I))) THEN
                VALUE(I) = DABS(A(J, I))
                LARGE(I) = J
            ENDIF
        ENDDO
    ENDDO
END
```

### Figure 1.2 Matrix Multiplication

```fortran
SUBROUTINE MATMAL(A, B, C, N)
    DOUBLE PRECISION A(N, N), B(N, N), C(N, N)
    INTEGER N, I, J, K
    DO I = 1, N
        DO J = 1, N
            C(I, J) = 0.0
        ENDDO
    ENDDO
    DO I = 1, N
        DO J = 1, N
            DO K = 1, N
                C(I, J) = C(I, J) + A(I, K) * B(K, J)
            ENDDO
        ENDDO
    ENDDO
END
```

### Figure 1.3 Maximum Monotone Subsequence

```fortran
INTEGER FUNCTION MONOTONE(A, N)
    DOUBLE PRECISION A(N)
    INTEGER C(N), CMAX
    INTEGER I, J, N
    C(N) = 1
    CMAX = 1
    DO I = N - 1, 1, -1
        C(I) = 1
        DO J = I + 1, N
            IF ((X(I) <= (X(J)).AND.(C(I) <= C(J) + 1))) THEN
                C(I) = C(J) + 1
            ENDIF
        ENDDO
        IF (CMAX <= C(I)) THEN
            CMAX = C(I)
        ENDIF
    ENDDO
    MONOTONE = CMAX
END
```

### Figure 1.4 Recursive Binary Search

```fortran
INTEGER FUNCTION BINARYSEARCH(A, N, L, U, KEY)
    DOUBLE PRECISION A(N), KEY
    INTEGER L, U, N
    INTEGER M
    IF (U < L) THEN
        BINARYSEARCH = 0
    ELSE
        M = (L + U) / 2
        IF (A(M) = KEY) THEN
            BINARYSEARCH = M
        ELSIF (A(M) < KEY) THEN
            BINARYSEARCH = BINARYSEARCH(A, N, L, M - 1, KEY)
        ELSE
            BINARYSEARCH = BINARYSEARCH(A, N, M + 1, U, KEY)
        ENDIF
    ENDIF
END
```
