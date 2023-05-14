# Mid-Level Intermediate Representation (MIR) and HIR Lowering

While the High-Level Intermediate Representation (HIR) has been constructed after type checking and
name resolution, it still too closely resembles the Abstract Syntax Tree (AST) for optimizing passes
to effectively work on.

Representing the program in tree form closely resembles the orginal program, but representing the
program as abstract machine instructions make many optimizaton algorithms easier. We can combine
the strengths of tree-shaped Intermediate Representation (IR) and machine instruction style IR
into a hybrid IR called the **Mid-Level Intermediate Representation** (**MIR**) by:

- Representing a procedure as a **flow graph** of sequences of instructions for an abstract RISC
  processor (the "Abstract Machine").
- The Abstract Machine has infinite supply of registers known as **temporaries**.
- There is a set of **instructions** for manipulating various data types.

When tree-based algorithms are applicable, the procedure is transformed into
**Static Single Assignment** (SSA) form. When the flow graph is converted to SSA form the expression
trees and nested loop structures are reconstructed.

## MIR

### Instructions

Each **instruction** for the Abstract Machine consists of:

- Opcode
- Set of input operands
- Set of output targets which name the values that are being changed

Some instructions may have constant or temporary operands: the set of temporaries is assumed to be
infinitely large. Each temporary contains a value for a span of execution of the procedure.

### From Instructions to Basic Blocks

Execution starts with the first instruction, executed sequentially until a branching instruction is
encountered. Instructions are partitioned into sequences called **Basic Blocks** (BB). BBs have the
following properties:

- Only the first instruction in a BB is the destination of a branching instruction.
- Only the last instructions in a BB are branching instructions.
- At the end of a BB there is a branching instructions which encodes every possible path out of the
  BB.

### From Basic Blocks to the Flow Graph

The Basic Blocks become nodes in a **flow graph** (a directed graph; cycles are permitted).

- The edges between blocks represent possible execution paths leaving the block. An edge
  \\( (B_{1}, B_{2}) \\) encodes that there is an execution path that can travel from
  \\( B_{1} \\) to \\( B_{2} \\).
- The flow graph has two special nodes: the **Start Block** and the **Exit Block**.
    - The Start Block only has outgoing edges. Execution must start from the Start Block.
    - The Exit Block only has incoming edges. Execution must end at the Exit Block.
