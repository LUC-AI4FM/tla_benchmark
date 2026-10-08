MODULE PlusCalTranslator

EXTENDS Naturals, Sequences, TLC, Temporal

CONSTANT FairnessOption

VARIABLES ast, lexemes, translationDone

(* Constants for fairness options *)
FairnessNoFairness == "NoFairness"
FairnessWeakFairProcess == "WeakFairProcess"
FairnessWeakFairNext == "WeakFairNext"
FairnessStrongFairProcess == "StrongFairProcess"

(* Initial AST constant *)
InitialAST == <<>>

(* Operator to check legality of AST - placeholder always true *)
IsLegalAST(a) == TRUE

(* Translation operators - placeholders returning simple strings *)
TranslateInit(a) == <<"INIT">>
TranslateNext(a) == <<"NEXT">>
TranslateSpec(a) == <<"SPEC">>
TranslateTermination(a) == <<"TERMINATION">>

(* Combine all translations into lexemes *)
TranslateAll(a) ==
  Append(TranslateInit(a),
         Append(TranslateNext(a),
                Append(TranslateSpec(a),
                       TranslateTermination(a))))

(* Next action *)
Next ==
  \/ translationDone = FALSE
     /\ LET newLex == TranslateAll(ast)
        IN  translationDone' = TRUE /\ lexemes' = newLex
  \/ translationDone = TRUE
     /\ translationDone' = TRUE /\ lexemes' = lexemes

(* Invariant: AST is legal *)
Invariant == IsLegalAST(ast)

(* Process action for fairness *)
processAction ==
  translationDone' = TRUE /\ translationDone = FALSE

(* Fairness conditions *)
FairnessCond ==
  CASE FairnessOption = FairnessNoFairness -> TRUE
       [] FairnessOption = FairnessWeakFairProcess ->
          WF_vars[processAction]
       [] FairnessOption = FairnessWeakFairNext ->
          WF_vars[Next]
       [] FairnessOption = FairnessStrongFairProcess ->
          SF_vars[processAction]

(* Specification *)
Spec ==
  Init
  /\ [][Next]_vars
  /\ Invariant
  /\ Termination
  /\ FairnessCond

Init ==
  /\ ast = InitialAST
  /\ lexemes = <<>>
  /\ translationDone = FALSE

Termination == <> translationDone

vars == <<ast, lexemes, translationDone>>