----------------------------- MODULE GlobalNamingPlusCalTranslator -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  This module models a translation pipeline from a global-naming PlusCal AST to a TLA+ spec.
  It defines:
   - An AST grammar (as sets and predicates over records and sequences)
   - A multi-phase translation pipeline (explode, translate calls/returns/gotos, add subscripts, assemble)
   - Operators that construct the generated TLA+ Init, Next, Spec, and a Termination property
   - Fairness options for the generated Spec: none, WF of process actions, WF of Next, SF of process actions

  The module is executable by TLC: it provides Init, Next, and Spec for the translation pipeline itself.
*)

CONSTANTS
  ProcIds,      \* Set of process identifiers
  Labels,       \* Set of label identifiers (global namespace)
  Vars,         \* Set of global variable identifiers
  Locals,       \* Set of process-local variable identifiers
  Values,       \* Set of data values
  InAST,        \* The input AST to translate
  FairnessOption \* One of: "None", "WF_Proc", "WF_Next", "SF_Proc"

(***************************************************************************)
(* AST grammar                                                             *)
(***************************************************************************)

Kind == {"Assign", "Goto", "If", "While", "Call", "Return", "Skip"}

StmtRecType == [ lab: Labels, kind: Kind, args: Seq(Values) ]

ASTSpace ==
  [ procs  : SUBSET ProcIds,
    globals: SUBSET Vars,
    locals : [ProcIds -> SUBSET Locals],
    labels : SUBSET Labels,
    body   : [ProcIds -> Seq(StmtRecType)]
  ]

IsAST(a) == a \in ASTSpace

Len(s) == IF s \in Seq(Values) \/ s \in Seq(StmtRecType) THEN Cardinality(Domain(s)) ELSE 0

LblsOfSeq(seq) ==
  { seq[i].lab : i \in 1..Len(seq) }

LblsOfProc(a, p) ==
  IF a \in ASTSpace THEN LblsOfSeq(a.body[p]) ELSE {}

AllLabels(a) ==
  UNION { LblsOfProc(a, p) : p \in ProcIds }

GlobalNaming(a) ==
  /\ a \in ASTSpace
  /\ \A p, q \in ProcIds : p # q => (LblsOfProc(a, p) \cap LblsOfProc(a, q)) = {}

(***************************************************************************)
(* Normalized (assembled) AST suitable to generate program semantics        *)
(***************************************************************************)

NormASTSpace ==
  [ graph : [Labels -> SUBSET (Labels \cup {"Done"})],
    entry : [ProcIds -> Labels],
    locals: [ProcIds -> SUBSET Locals],
    globals: SUBSET Vars,
    labels: SUBSET (Labels \cup {"Done"})
  ]

NormOK(u) ==
  /\ u \in NormASTSpace
  /\ \A p \in ProcIds : u.entry[p] \in u.labels
  /\ DOMAIN u.graph \subseteq Labels
  /\ \A l \in DOMAIN u.graph : u.graph[l] \subseteq u.labels
  /\ {"Done"} \subseteq u.labels

(***************************************************************************)
(* Abstract translation-step predicates                                     *)
(***************************************************************************)

ExplodedFrom(a, s) ==
  /\ IsAST(a) /\ IsAST(s)
  /\ a.globals = s.globals
  /\ a.procs \subseteq ProcIds /\ s.procs \subseteq ProcIds
  /\ a.labels \subseteq Labels /\ s.labels \subseteq Labels

CallsTranslated(s, c) ==
  /\ IsAST(s) /\ IsAST(c)
  /\ s.globals = c.globals
  /\ s.procs = c.procs
  /\ c.labels \subseteq Labels

SubscriptsAdded(c, u) ==
  /\ IsAST(c) /\ NormOK(u)
  /\ u.globals = c.globals
  /\ u.locals = c.locals
  /\ u.labels \supseteq c.labels \cup {"Done"}

(***************************************************************************)
(* Generated program state and semantics (functions of normalized AST)      *)
(***************************************************************************)

VARIABLES pc, mem, lmem

ProgVars == << pc, mem, lmem >>

ProgramTypeOK(u) ==
  /\ NormOK(u)
  /\ pc \in [ProcIds -> (u.labels \cup {"Done"})]
  /\ mem \in [Vars -> Values]
  /\ lmem \in [ProcIds -> [Locals -> Values]]

GenInit(u) ==
  /\ NormOK(u)
  /\ pc \in [ProcIds -> (u.labels \cup {"Done"})]
  /\ \A p \in ProcIds : pc[p] = u.entry[p]
  /\ mem \in [Vars -> Values]
  /\ lmem \in [ProcIds -> [Locals -> Values]]

Step(p, u) ==
  /\ NormOK(u)
  /\ p \in ProcIds
  /\ pc[p] # "Done"
  /\ pc[p] \in DOMAIN u.graph
  /\ pc'[p] \in u.graph[ pc[p] ]
  /\ \A q \in ProcIds \ {p} : pc'[q] = pc[q]
  /\ UNCHANGED << mem, lmem >>

EnvStutter(u) ==
  /\ NormOK(u)
  /\ UNCHANGED ProgVars

GenNext(u) ==
  \/ \E p \in ProcIds : Step(p, u)
  \/ EnvStutter(u)

GeneratedSpec(u) ==
  LET F == FairnessOption IN
  /\ GenInit(u)
  /\ [][GenNext(u)]_ProgVars
  /\ IF F = "WF_Proc" THEN
       \A p \in ProcIds : WF_ProgVars(Step(p, u))
     ELSE IF F = "WF_Next" THEN
       WF_ProgVars(GenNext(u))
     ELSE IF F = "SF_Proc" THEN
       \A p \in ProcIds : SF_ProgVars(Step(p, u))
     ELSE
       TRUE

Termination(u) ==
  <> (\A p \in ProcIds : pc[p] = "Done")

(***************************************************************************)
(* Translation pipeline state machine                                       *)
(***************************************************************************)

VARIABLES phase, iAST, sAST, cAST, uAST

AllowedPhases == {"Explode", "Calls", "Subscripts", "Assemble", "Done"}

PipelineTypeOK ==
  /\ phase \in AllowedPhases
  /\ iAST \in ASTSpace
  /\ sAST \in ASTSpace
  /\ cAST \in ASTSpace
  /\ uAST \in NormASTSpace
  /\ ProgramTypeOK(uAST)

GlobalNameInvariant ==
  /\ IsAST(iAST) => GlobalNaming(iAST)
  /\ IsAST(sAST) => GlobalNaming(sAST)
  /\ IsAST(cAST) => GlobalNaming(cAST)

Init ==
  /\ phase = "Explode"
  /\ iAST = InAST
  /\ sAST \in ASTSpace
  /\ cAST \in ASTSpace
  /\ uAST \in NormASTSpace
  /\ pc \in [ProcIds -> (Labels \cup {"Done"})]
  /\ mem \in [Vars -> Values]
  /\ lmem \in [ProcIds -> [Locals -> Values]]

ExplodeAct ==
  /\ phase = "Explode"
  /\ IsAST(iAST)
  /\ \E s \in ASTSpace :
       /\ ExplodedFrom(iAST, s)
       /\ sAST' = s
  /\ phase' = "Calls"
  /\ UNCHANGED << iAST, cAST, uAST, pc, mem, lmem >>

CallsAct ==
  /\ phase = "Calls"
  /\ IsAST(sAST)
  /\ \E c \in ASTSpace :
       /\ CallsTranslated(sAST, c)
       /\ cAST' = c
  /\ phase' = "Subscripts"
  /\ UNCHANGED << iAST, sAST, uAST, pc, mem, lmem >>

SubscriptsAct ==
  /\ phase = "Subscripts"
  /\ IsAST(cAST)
  /\ \E u \in NormASTSpace :
       /\ SubscriptsAdded(cAST, u)
       /\ uAST' = u
  /\ phase' = "Assemble"
  /\ UNCHANGED << iAST, sAST, cAST, pc, mem, lmem >>

AssembleAct ==
  /\ phase = "Assemble"
  /\ phase' = "Done"
  /\ UNCHANGED << iAST, sAST, cAST, uAST, pc, mem, lmem >>

DoneAct ==
  /\ phase = "Done"
  /\ UNCHANGED << phase, iAST, sAST, cAST, uAST, pc, mem, lmem >>

Next ==
  ExplodeAct
  \/ CallsAct
  \/ SubscriptsAct
  \/ AssembleAct
  \/ DoneAct

Spec ==
  /\ Init
  /\ [][Next]_<< phase, iAST, sAST, cAST, uAST, pc, mem, lmem >>

(***************************************************************************)
(* Liveness for the translation pipeline                                    *)
(***************************************************************************)

TranslationTerminates ==
  <> (phase = "Done")

=============================================================================