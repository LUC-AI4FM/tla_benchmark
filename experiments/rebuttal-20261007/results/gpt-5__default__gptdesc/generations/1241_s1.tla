----------------------------- MODULE PlusCal_Translator -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

(*
This module models a translation from a global-naming PlusCal abstract syntax tree (AST)
to a sequence of lexemes (strings) representing the generated TLA+ output. It provides:
- A grammar of legal ASTs for algorithms, procedures, processes, and labeled statements.
- Operators that translate an AST into output lexeme sequences for Init, Next, Spec,
  and a Termination property.
- Modeling of fairness options for the generated Spec:
    "None", "WF_Procs", "WF_Next", "SF_Procs"
- An executable state machine that incrementally emits the output, suitable for TLC.
- Safety invariants (well-formedness, uniqueness, prefix/equality of emitted output).
- A liveness property stating that the translator terminates (eventually reaches Done).
*)

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)

CONSTANTS
  ProcIdSet,      \* Universe of process identifiers for AST processes
  AST,            \* Input abstract syntax tree (see WellFormedAlgorithm for grammar)
  FairnessMode    \* One of the supported fairness modes (see FairnessModes)

(***************************************************************************)
(* Basic sets and helpers                                                  *)
(***************************************************************************)

Lexeme == STRING

FairnessModes == {"None", "WF_Procs", "WF_Next", "SF_Procs"}

IsStringSeq(s) == s \in Seq(STRING)

Cat(S) ==
  IF S = <<>> THEN <<>>
  ELSE Head(S) \o Cat(Tail(S))

ElemsOfSeq(S) == { S[i] : i \in DOMAIN S }

(***************************************************************************)
(* AST grammar                                                             *)
(***************************************************************************)

(*
Records (informal shape):
- VarDecl       == [name: STRING, init: any-value]
- LabeledStmt   == [label: STRING, actionName: STRING, target: Seq(STRING)]
- Procedure     == [name: STRING, params: Seq(STRING), locals: Seq(VarDecl), body: Seq(LabeledStmt)]
- Process       == [name: STRING, ids: SUBSET ProcIdSet, locals: Seq(VarDecl), body: Seq(LabeledStmt)]
- Algorithm     == [name: STRING, vars: Seq(VarDecl), procedures: Seq(Procedure), processes: Seq(Process)]
*)

IsVarDecl(v) ==
  /\ v \in [name: STRING, init: CHOOSE x : TRUE]
  /\ DOMAIN v = {"name","init"}
  /\ v.name \in STRING

IsLabeledStmt(s) ==
  /\ s \in [label: STRING, actionName: STRING, target: Seq(STRING)]
  /\ DOMAIN s = {"label","actionName","target"}
  /\ s.label \in STRING
  /\ s.actionName \in STRING
  /\ IsStringSeq(s.target)

IsProcedure(p) ==
  /\ p \in [name: STRING, params: Seq(STRING), locals: Seq(CHOOSE r : TRUE), body: Seq(CHOOSE r : TRUE)]
  /\ DOMAIN p = {"name","params","locals","body"}
  /\ p.name \in STRING
  /\ IsStringSeq(p.params)
  /\ p.locals \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN p.locals : IsVarDecl(p.locals[i])
  /\ p.body \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN p.body : IsLabeledStmt(p.body[i])
  /\ UniqueRecordNames(p.locals)
  /\ UniqueLabelsOfBody(p.body)

IsProcess(pr) ==
  /\ pr \in [name: STRING, ids: SUBSET ProcIdSet, locals: Seq(CHOOSE r : TRUE), body: Seq(CHOOSE r : TRUE)]
  /\ DOMAIN pr = {"name","ids","locals","body"}
  /\ pr.name \in STRING
  /\ pr.ids \subseteq ProcIdSet
  /\ pr.locals \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN pr.locals : IsVarDecl(pr.locals[i])
  /\ pr.body \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN pr.body : IsLabeledStmt(pr.body[i])
  /\ UniqueRecordNames(pr.locals)
  /\ UniqueLabelsOfBody(pr.body)

IsAlgorithm(a) ==
  /\ a \in [name: STRING, vars: Seq(CHOOSE r : TRUE), procedures: Seq(CHOOSE r : TRUE), processes: Seq(CHOOSE r : TRUE)]
  /\ DOMAIN a = {"name","vars","procedures","processes"}
  /\ a.name \in STRING
  /\ a.vars \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN a.vars : IsVarDecl(a.vars[i])
  /\ a.procedures \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN a.procedures : IsProcedure(a.procedures[i])
  /\ a.processes \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN a.processes : IsProcess(a.processes[i])
  /\ UniqueRecordNames(a.vars)
  /\ UniqueRecordNames(a.procedures)
  /\ UniqueRecordNames(a.processes)
  /\ GlobalLabelsUnique(a)
  /\ AllTargetsReferToGlobalLabels(a)

UniqueRecordNames(S) ==
  /\ S \in Seq(CHOOSE r : TRUE)
  /\ Cardinality({ S[i].name : i \in DOMAIN S }) = Len(S)

UniqueLabelsOfBody(body) ==
  /\ body \in Seq(CHOOSE r : TRUE)
  /\ \A i \in DOMAIN body : IsLabeledStmt(body[i])
  /\ Cardinality({ body[i].label : i \in DOMAIN body }) = Len(body)

LabelSetOfBody(body) == { body[i].label : i \in DOMAIN body }
TargetSetOfStmt(s) == { s.target[j] : j \in DOMAIN s.target }
TargetSetOfBody(body) == UNION { TargetSetOfStmt(body[i]) : i \in DOMAIN body }

AllProcedureBodies(a) == { a.procedures[i].body : i \in DOMAIN a.procedures }
AllProcessBodies(a)   == { a.processes[i].body  : i \in DOMAIN a.processes }

GlobalLabelSet(a) ==
  LET procLs == UNION { LabelSetOfBody(b) : b \in AllProcessBodies(a) } IN
  LET procTs == UNION { TargetSetOfBody(b) : b \in AllProcessBodies(a) } IN
  LET procAll == procLs \cup procTs IN
  LET procLs2 == UNION { LabelSetOfBody(b) : b \in AllProcedureBodies(a) } IN
  LET procTs2 == UNION { TargetSetOfBody(b) : b \in AllProcedureBodies(a) } IN
  procAll \cup procLs2 \cup procTs2

GlobalLabelsUnique(a) ==
  /\ IsAlgorithm(a)
  /\ Cardinality(GlobalLabelSet(a)) =
       Cardinality(UNION { LabelSetOfBody(b) : b \in AllProcessBodies(a) })
     + Cardinality(UNION { LabelSetOfBody(b) : b \in AllProcedureBodies(a) })
     \* No label appears more than once as a definition; allows targets to reuse names but doesn't add new ones.

AllTargetsReferToGlobalLabels(a) ==
  /\ IsAlgorithm(a)
  /\ \A b \in AllProcessBodies(a) :
        TargetSetOfBody(b) \subseteq GlobalLabelSet(a)
  /\ \A b \in AllProcedureBodies(a) :
        TargetSetOfBody(b) \subseteq GlobalLabelSet(a)

WellFormedAlgorithm(a) == IsAlgorithm(a)

(***************************************************************************)
(* Extraction helpers for translation                                      *)
(***************************************************************************)

VarNames(a) == [ i \in DOMAIN a.vars |-> a.vars[i].name ]

ProcActionNames(pr) == [ i \in DOMAIN pr.body |-> pr.body[i].actionName ]

AllProcessActionNames(a) ==
  Cat([ i \in DOMAIN a.processes |-> ProcActionNames(a.processes[i]) ])

(***************************************************************************)
(* Emission of output lexemes (translation result)                         *)
(***************************************************************************)

EmitHeader(a) ==
  << "----", "MODULE", a.name, "----" >>

EmitVariables(a) ==
  << "VARIABLES" >> \o [ i \in DOMAIN a.vars |-> a.vars[i].name ]

EmitInit(a) ==
  << "Init", "==", "(* initial values elided *)" >>

EmitNext(a) ==
  << "Next", "==", "(* disjunction of process actions elided *)" >>

FairnessChunk(a, m) ==
  CASE m = "None" ->
         << >>
    [] m = "WF_Procs" ->
         Cat([ i \in DOMAIN AllProcessActionNames(a)
               |-> << "/\\", "WF_vars(", AllProcessActionNames(a)[i], ")" >> ])
    [] m = "WF_Next" ->
         << "/\\", "WF_vars(", "Next", ")" >>
    [] m = "SF_Procs" ->
         Cat([ i \in DOMAIN AllProcessActionNames(a)
               |-> << "/\\", "SF_vars(", AllProcessActionNames(a)[i], ")" >> ])
    [] OTHER ->
         << >>

EmitSpec(a, m) ==
  << "Spec", "==",
     "Init", "/\\", "[]", "[", "Next", "]_", "vars"
  >> \o FairnessChunk(a, m)

EmitTerminationProperty(a) ==
  << "Termination", "==", "<>", "Done" >>

Segments(a, m) ==
  << EmitHeader(a), EmitVariables(a), EmitInit(a), EmitNext(a), EmitSpec(a, m), EmitTerminationProperty(a) >>

OutExpected(a, m) == Cat(Segments(a, m))

(***************************************************************************)
(* Translator machine state and behavior                                    *)
(***************************************************************************)

VARIABLES out, phase

Phases == {"Start","Header","Vars","Init","Next","Spec","Termination","Done"}

KOfPhase(p) ==
  CASE p = "Start" -> 0
    [] p = "Header" -> 1
    [] p = "Vars" -> 2
    [] p = "Init" -> 3
    [] p = "Next" -> 4
    [] p = "Spec" -> 5
    [] p \in {"Termination","Done"} -> 6
    [] OTHER -> 0

ExpectedOutForPhase(a, m, p) ==
  LET segs == Segments(a, m) IN
  LET k == KOfPhase(p) IN
  IF k = 0 THEN <<>> ELSE Cat(SubSeq(segs, 1, k))

Init ==
  /\ phase = "Start"
  /\ out = <<>>

Next ==
  \/ /\ phase = "Start"
     /\ out' = EmitHeader(AST)
     /\ phase' = "Header"
  \/ /\ phase = "Header"
     /\ out' = out \o EmitVariables(AST)
     /\ phase' = "Vars"
  \/ /\ phase = "Vars"
     /\ out' = out \o EmitInit(AST)
     /\ phase' = "Init"
  \/ /\ phase = "Init"
     /\ out' = out \o EmitNext(AST)
     /\ phase' = "Next"
  \/ /\ phase = "Next"
     /\ out' = out \o EmitSpec(AST, FairnessMode)
     /\ phase' = "Spec"
  \/ /\ phase = "Spec"
     /\ out' = out \o EmitTerminationProperty(AST)
     /\ phase' = "Termination"
  \/ /\ phase = "Termination"
     /\ UNCHANGED out
     /\ phase' = "Done"
  \/ /\ phase = "Done"
     /\ UNCHANGED << out, phase >>

Spec ==
  Init /\ [][Next]_<< out, phase >>

(***************************************************************************)
(* Assumptions on constants (grammar and fairness mode)                    *)
(***************************************************************************)

ASSUME /\ FairnessMode \in FairnessModes
       /\ WellFormedAlgorithm(AST)

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

TypeOK ==
  /\ phase \in Phases
  /\ out \in Seq(Lexeme)
  /\ FairnessMode \in FairnessModes
  /\ WellFormedAlgorithm(AST)

PrefixOK ==
  out = ExpectedOutForPhase(AST, FairnessMode, phase)

NamesUnique ==
  /\ UniqueRecordNames(AST.vars)
  /\ UniqueRecordNames(AST.procedures)
  /\ UniqueRecordNames(AST.processes)

LabelsUnique ==
  GlobalLabelsUnique(AST)

TargetsOK ==
  AllTargetsReferToGlobalLabels(AST)

AllSafetyInvariants ==
  /\ TypeOK /\ PrefixOK /\ NamesUnique /\ LabelsUnique /\ TargetsOK

(***************************************************************************)
(* Liveness property (termination of the translator)                       *)
(***************************************************************************)

Termination ==
  <> (phase = "Done")

=============================================================================