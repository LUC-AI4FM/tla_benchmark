------------------------------ MODULE CalToTla ------------------------------
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------------*)
(*  Constants required by the configuration                                 *)
(*--------------------------------------------------------------------------*)

CONSTANT Object, Any

(*--------------------------------------------------------------------------*)
(*  Basic types used in the specification                                  *)
(*--------------------------------------------------------------------------*)

Lexeme == Symbol
SeqLexeme == Seq(Lexeme)

(*  A node of a +CAL abstract syntax tree.  The fields are kept minimal   *)
Node == [ type : Symbol,
          value : ANY,
          children : Seq(Node) ]

(*--------------------------------------------------------------------------*)
(*  Grammar:  predicate that checks whether a given node is a well‑formed   *)
(*  +CAL AST.  Only the structure of the check is sketched; the full       *)
(*  grammar would be considerably larger.                                 *)
(*--------------------------------------------------------------------------*)

Grammar(node : Node) == 
  /\ node.type \in {"Alg", "Proc", "Stmt", "Assign", "While",
                    "If", "Either", "With", "Call", "Return",
                    "Goto", "Skip", "Print", "Assert"}
  /\ IF node.type = "Alg" THEN
       /\ node.children # <<>> 
       /\ \A child \in node.children : Grammar(child)
     ELSE
       TRUE

(*--------------------------------------------------------------------------*)
(*  Fairness options for the translation.  These are just symbolic values   *)
(*  that will be passed to Translation.                                     *)
(*--------------------------------------------------------------------------*)

FairnessOption == {"none", "weakPerAction", "weakWhole", "strongPerAction"}

(*--------------------------------------------------------------------------*
 *  Translation:  given an AST and a fairness option, produce the sequence
 *  of lexemes that form a valid TLA+ specification.
 *
 *  The translation is intentionally high‑level; it demonstrates how one
 *  might construct the various parts of a TLA+ spec (variable declarations,
 *  Init, per‑label actions, Next, Spec, Termination) from an AST.  The
 *  actual code generation logic is omitted for brevity.
 *
 *--------------------------------------------------------------------------*)

Translation(ast : Node, fairness : FairnessOption) == 
  LET
    (* 1. Variable declaration section *)
    VarDecls == 
      IF Grammar(ast) THEN
        "VARIABLES" \o "vars"
      ELSE
        "VARIABLES" \o "error"

    (* 2. Init predicate *)
    InitPred == 
      IF fairness = "none" THEN
        "Init == /\ vars = <<>>"
      ELSE
        "Init == /\ vars' = vars"

    (* 3. Per‑label action definitions (simplified) *)
    LabelActions == 
      "LabelActions == \{ ... \}"

    (* 4. Next‑state action *)
    NextAct == 
      IF fairness = "weakWhole" THEN
        "Next == /\ UNCHANGED vars"
      ELSE
        "Next == /\ vars' = vars"

    (* 5. Spec formula *)
    SpecForm == 
      "Spec == Init /\ [][Next]_vars"

    (* 6. Termination property (placeholder) *)
    TermProp == 
      "Termination == \A i : vars[i] = 0"

    (* 7. Assemble the lexeme sequence *)
    LexSeq == 
      << VarDecls, InitPred, LabelActions,
         NextAct, SpecForm, TermProp >>
  IN
    LexSeq

(*--------------------------------------------------------------------------*)
(*  Example usage (not part of the spec but useful for testing)             *)
(*--------------------------------------------------------------------------*)

ExampleAST == [ type |-> "Alg",
                value |-> <<>>,
                children |-> <<>> ]

ExampleLexemes == Translation(ExampleAST, "none")

=============================================================================