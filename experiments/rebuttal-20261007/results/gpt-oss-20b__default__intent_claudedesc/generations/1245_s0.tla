------------------------------ MODULE CalToTla ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT FairnessOption \in {"none", "weakPerAction", "weakWholeNext", "strongPerAction"}
CONSTANTS NextLabel, LabelBody   (* uninterpreted functions *)

VARIABLES ast, lexemes, pc, stack, vars

(* ------------------------------------------------------------------ *)
(* Types for AST nodes (simplified) *)
Node == [kind : String]
Program == [kind |-> "Program", procs : Seq(Node)]
Procedure == [kind |-> "Procedure",
              name  : String,
              body  : Seq(Node),
              labels: Set(String)]

Labels(a) ==
    IF a.kind = "Program" THEN
        \E p \in a.procs: Labels(p)
    ELSEIF a.kind = "Procedure" THEN
        a.labels
    ELSE
        {}

LabeledActions == { LabeledAction(l) : l \in Labels(ast) }

(* ------------------------------------------------------------------ *)
(* Translation operator (abstract placeholder) *)
Translate(a) ==
    IF a.kind = "Program" THEN
        SeqConcat([ Translate(p) :> p \in a.procs ])
    ELSEIF a.kind = "Procedure" THEN
        << "PROC", a.name, "(", ")", "BEGIN",
           SeqConcat([ Translate(s) :> s \in a.body ]),
           "END" >>
    ELSE
        << >>

(* ------------------------------------------------------------------ *)
(* Actions for each label (simplified) *)
LabeledAction(l) ==
    /\ pc = l
    /\ pc' = NextLabel(pc, ast)
    /\ lexemes' = SeqConcat(lexemes, Translate(LabelBody(ast,l)))
    /\ UNCHANGED <<ast, stack, vars>>

(* ------------------------------------------------------------------ *)
(* Initial state *)
Init ==
    /\ ast = <<>>
    /\ lexemes = <<>>
    /\ pc = "START"
    /\ stack = <<>>
    /\ vars = [v \in {} -> 0]

(* ------------------------------------------------------------------ *)
(* Next-state action: either advance a label or finish translation *)
Next ==
    \/ \E l \in Labels(ast) : LabeledAction(l)
    \/ /\ pc = "END"
       /\ lexemes' = Translate(ast)

(* ------------------------------------------------------------------ *)
(* Fairness conditions *)
FairnessCond ==
    CASE FairnessOption = "none" -> TRUE
         [] FairnessOption = "weakPerAction" -> WEAK FAIRNESS LabeledActions
         [] FairnessOption = "weakWholeNext" -> WEAK FAIRNESS Next
         [] FairnessOption = "strongPerAction" -> STRONG FAIRNESS LabeledActions

(* ------------------------------------------------------------------ *)
(* Safety invariants (trivial placeholder) *)
Safety == TRUE

(* ------------------------------------------------------------------ *)
(* Termination property *)
Termination == <> (pc = "END")

(* ------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<ast, lexemes, pc, stack, vars>> /\ FairnessCond /\ Termination
=============================================================================