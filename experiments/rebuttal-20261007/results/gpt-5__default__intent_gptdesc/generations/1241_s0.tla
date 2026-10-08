----------------------------- MODULE Translator -----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
  \* Basic universes
  Id, Val, Label, ProcId,
  \* Catalogs
  ErrorKinds, FairnessModes,
  \* A set of abstract transition systems used as a semantic carrier for both source and target
  TS,
  \* Designated "no output yet" marker
  NoTarget,
  \* The input abstract-syntax tree (parse tree) of the source program
  InputAST,

  \* Uninterpreted, total operator-constants capturing abstract structure/semantics and translation
  WellFormed(_),               \* Well-formedness checker for an AST
  Errors(_),                   \* Returns a subset of ErrorKinds detailing detected issues in an AST

  \* Source semantics as a transition system
  SrcSemantics(_),             \* Yields an element of TS describing the source program semantics (control, data, procedures, etc.)

  \* Translator proper: produces a target transition system that explicitly encodes control points, data state, call-stacks, etc.
  Translate(_),                \* Yields an element of TS describing the translated target spec

  \* Abstract semantic-correctness relations (predicates over TS and/or AST)
  EquivalentBehaviors(_, _),           \* Semantic equivalence up to representation choices
  HasControlPoints(_),                 \* Target TS represents program control points explicitly
  HasDataState(_),                     \* Target TS represents data state (globals/locals) explicitly
  InitFromDecls(_, _),                 \* Target TS initializes from declared initializers
  PreservesNextTransitions(_, _),      \* Target TS preserves the possible next-state transitions of each source statement
  CallsReturnsEncodedCorrectly(_, _),  \* Call stacks and returns behave correctly across nested calls and processes
  FairnessSupportedInTarget(_, _),     \* Optional fairness constraints (process-level or global) are supported/encoded
  FinalStatesPreserved(_, _),          \* Final/terminal-state behavior is preserved
  SafetyPropsPreserved(_, _)           \* Source invariants/assertions are preserved in the target

\* Expected error kinds that the translator can detect (must be a subset of the provided ErrorKinds catalog)
ExpectedErrorKinds == {
  "DuplicateDeclaration",
  "NonConstantInitializer",
  "IllegalLocalUse",
  "UnknownName",
  "MissingLabel",
  "InvalidReturn",
  "ArityMismatch",
  "TypeMismatch"
}

ASSUME /\ ExpectedErrorKinds \subseteq ErrorKinds
       /\ TS # {} 
       \* Optional sanity assumptions about universes (not strictly required)
       /\ Id # {} /\ Val # {} /\ Label # {} /\ ProcId # {}
       \* Abstract postulates relating the carriers:
       \* Source and target semantics are both elements of TS
       /\ SrcSemantics(InputAST) \in TS
       \* Translation produces a TS whenever the input is well-formed
       /\ WellFormed(InputAST) => Translate(InputAST) \in TS

\* Translator control stages
Stages == {"Start","Checking","Translating","Done","Error"}

VARIABLES stage, target, errset

vars == << stage, target, errset >>

Init ==
  /\ stage = "Start"
  /\ target = NoTarget
  /\ errset = {}

\* Actions modeling the translator's operation
Check ==
  /\ stage = "Start"
  /\ stage' = "Checking"
  /\ UNCHANGED << target, errset >>

Analyze ==
  /\ stage = "Checking"
  /\ errset' = Errors(InputAST)
  /\ IF errset' = {} THEN stage' = "Translating" ELSE stage' = "Error"
  /\ UNCHANGED target

DoTranslate ==
  /\ stage = "Translating"
  /\ target' = Translate(InputAST)
  /\ stage' = "Done"
  /\ UNCHANGED errset

Stutter ==
  /\ stage \in {"Done","Error"}
  /\ UNCHANGED vars

Next == Check \/ Analyze \/ DoTranslate \/ Stutter

\* Safety invariants required of any behavior of the translator
SafetyInv ==
  /\ stage \in Stages
  /\ errset \subseteq ErrorKinds
  /\ ~(stage = "Done" /\ stage = "Error")
  /\ (stage = "Done" => target \in TS)
  /\ (stage # "Done" => target = NoTarget)
  /\ (stage = "Done" => WellFormed(InputAST))
  /\ (stage = "Error" => errset = Errors(InputAST))

\* Semantic-correctness obligations that must hold once translation succeeds
CorrectnessInv ==
  stage = "Done" =>
    /\ EquivalentBehaviors(SrcSemantics(InputAST), target)
    /\ HasControlPoints(target)
    /\ HasDataState(target)
    /\ InitFromDecls(InputAST, target)
    /\ PreservesNextTransitions(InputAST, target)
    /\ CallsReturnsEncodedCorrectly(InputAST, target)
    /\ FairnessSupportedInTarget(InputAST, target)
    /\ FinalStatesPreserved(InputAST, target)
    /\ SafetyPropsPreserved(InputAST, target)

\* Progress/liveness expectations:
\* - If the input is well-formed, the translator eventually finishes successfully.
\* - If the input is ill-formed, the translator eventually reports the precise error set.
ProgressProp ==
  /\ ( WellFormed(InputAST)  => <> (stage = "Done") )
  /\ (~WellFormed(InputAST) => <> (stage = "Error" /\ errset = Errors(InputAST)) )

\* The overall system specification includes safety, semantic-correctness, and progress via action fairness.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Check)
  /\ WF_vars(Analyze)
  /\ WF_vars(DoTranslate)
  /\ []SafetyInv
  /\ []CorrectnessInv
  /\ ProgressProp

=============================================================================