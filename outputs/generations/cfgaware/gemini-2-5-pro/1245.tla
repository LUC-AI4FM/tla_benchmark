---- MODULE PlusCalTranslator ----
EXTENDS TLC, Sequences, FiniteSets, Records

(*
This module specifies the translation from the abstract syntax tree (AST) of a
global-naming PlusCal algorithm into its corresponding TLA+ specification. It
defines the AST grammar as sets and predicates over records and sequences, and
then defines a translation pipeline. The pipeline's conceptual stages are:
exploding structured labeled statements, translating calls/returns/gotos, and
adding subscripts for process-local variables. Finally, it constructs the TLA+
operators Init, Next, Spec, and a Termination property.

The file also models fairness options for the translation output, supporting
no fairness, weak fairness of process actions, weak fairness of Next, and
strong fairness of process actions. It is written to be executable by TLC.

Limitations and Hacks:
- This is a meta-specification; it defines the *translation*, not a state
  machine that performs the translation. The translation is represented by a
  series of functional operators.
- The expression language is not parsed; expressions are treated as opaque
  objects (typically strings).
- The AST is a simplified model of PlusCal, lacking features like procedures,
  macros, `with`, `while`, etc. The pipeline is similarly simplified to
  demonstrate the concept rather than provide a full implementation. For
  example, `if` statements are not recursively exploded but are handled by a
  special statement type in the "flattened" AST.
- The sets `Object` and `Any` must be defined as small, finite sets in the
  model configuration for TLC to execute this specification.
*)

CONSTANT
    \* The set of all "objects" in the PlusCal source: identifiers, literals, etc.
    Object,

    \* The set of all possible values a variable can hold in the target spec.
    Any,

    \* A sample PlusCal algorithm represented as an Abstract Syntax Tree (AST).
    InputAlgorithm,

    \* The set of process identifiers.
    Procs,

    \* The fairness option to use for the generated specification.
    FairnessOption

ASSUME FairnessOption \in {"none", "weak_process", "weak_next", "strong_process"}

\*=============================================================================