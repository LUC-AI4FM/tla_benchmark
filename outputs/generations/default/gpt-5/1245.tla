----------------------------- MODULE PlusCalTranslation -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Specification of a translation from a global-naming PlusCal AST to a TLA+ specification.
  The executable part (Init/Next/Spec) models the translated program using a flat,
  label-based control-flow graph with calls/returns and per-process local variable subscripting.
*)

CONSTANTS
  P,            \* Set of process identifiers
  Labels,       \* Set of globally-unique labels
  SharedVars,   \* Set of shared variable names
  LocalVars,    \* Set of process-local variable names
  Values,       \* Value domain for all variables
  AST,          \* Original abstract syntax tree (uninterpreted here)
  Start,        \* Start label per process: a function P -> Labels
  FlatProg,     \* Flat, exploded labeled program after translation pipeline (see FlatProgOK)
  FairnessOption  \* One of {"None","WFProcs","WFNext","SFProcs"}

(*
  Grammar for the flat program produced by the translation pipeline.

  Each label maps to a record with fields:
    owner   : process that owns this (globally named) label
    tag     : one of {"Action","Branch","Goto","Call","Return","Done"}
    succ    : set of successor labels (empty for Return/Done; singleton for Goto/Call)
    callee  : entry label of target procedure for Call; a distinguished NULL otherwise
    wShared : subset of SharedVars that this label may write
    wLocal  : subset of LocalVars that this label may write (for the current process)
*)
TagSet == {"Action","Branch","Goto","Call","Return","Done"}
NULL == "NULL"

FlatRecordType ==
  [ owner   : P,
    tag     : TagSet,
    succ    : SUBSET Labels,
    callee  : Labels \cup {NULL},
    wShared : SUBSET SharedVars,
    wLocal  : SUBSET LocalVars ]

FlatProgOK(F) ==
  /\ F \in [Labels -> FlatRecordType]
  /\ \A l \in Labels:
       LET r == F[l] IN
         /\ IF r.tag \in {"Goto","Call"} THEN Cardinality(r.succ) = 1
            ELSE IF r.tag \in {"Return","Done"} THEN r.succ = {}
            ELSE r.succ \subseteq Labels
         /\ IF r.tag = "Call" THEN r.callee \in Labels ELSE r.callee \in {NULL}
         /\ \A l2 \in r.succ: F[l2].owner = r.owner

StartOK(F) ==
  /\ Start \in [P -> Labels]
  /\ \A p \in P: F[Start[p]].owner = p

ASSUME
  /\ Values # {}
  /\ FairnessOption \in {"None","WFProcs","WFNext","SFProcs"}
  /\ FlatProgOK(FlatProg)
  /\ StartOK(FlatProg)

(*
  Abstract syntax tree grammar and translation pipeline (symbolic).
  These operators document the intended structure; they are not used by Next.
*)

IsStmt(s) ==
  /\ s \in [
      tag     : {"Skip","Assign","Goto","If","While","Either","Call","Return","Done"},
      lab     : Labels,
      fields  : SUBSET {"expr","writes","guards","bodies","target","proc","entry"}]

IsAST(ast) ==
  /\ ast \in [Labels -> [tag: STRING, lab: Labels, fields: SUBSET STRING]]
  /\ \A l \in DOMAIN ast: IsStmt(ast[l])

ExplodeStructured(ast) ==
  CHOOSE f \in [Labels -> FlatRecordType]:
    /\ \A l \in DOMAIN ast: f[l].owner \in P
    /\ \A l \in DOMAIN ast:
         LET s == ast[l] IN
           IF s.tag \in {"If","While","Either"} THEN f[l].tag \in {"Branch","Action"}
           ELSE TRUE

TranslateCalls(f) ==
  f

AddProcessSubscripts(f) ==
  [l \in Labels |-> [f[l] EXCEPT !.wLocal = f[l].wLocal, !.wShared = f[l].wShared]]

Translated ==
  AddProcessSubscripts(TranslateCalls(ExplodeStructured(AST)))

(*
  State variables of the translated TLA+ specification.
  - pc[p] is the current control label of process p
  - stack[p] is a sequence of return labels for p (call stack)
  - shared is a total function over shared variables
  - local[p] is a total function over local variables of p
*)
VARIABLES pc, stack, shared, local

vars == << pc, stack, shared, local >>

Owner(l) == FlatProg[l].owner
Tag(l) == FlatProg[l].tag
Succ(l) == FlatProg[l].succ
Callee(l) == FlatProg[l].callee
WShared(l) == FlatProg[l].wShared
WLocal(l) == FlatProg[l].wLocal

The(S) == CHOOSE x \in S: TRUE

TypeOK ==
  /\ pc \in [P -> Labels]
  /\ \A p \in P: Owner(pc[p]) = p
  /\ stack \in [P -> Seq(Labels)]
  /\ \A p \in P: \A i \in 1..Len(stack[p]): stack[p][i] \in Labels
  /\ shared \in [SharedVars -> Values]
  /\ local \in [P -> [LocalVars -> Values]]

PCOwnerInv ==
  \A p \in P: Owner(pc[p]) = p

ReturnStackOk ==
  \A p \in P: Tag(pc[p]) = "Return" => Len(stack[p]) > 0

DoneStackEmpty ==
  \A p \in P: Tag(pc[p]) = "Done" => Len(stack[p]) = 0

Init ==
  /\ pc = Start
  /\ stack = [p \in P |-> <<>>]
  /\ shared \in [SharedVars -> Values]
  /\ local \in [P -> [LocalVars -> Values]]

ProcStep(p) ==
  LET l == pc[p] IN
  IF Tag(l) \in {"Action","Branch","Goto"} THEN
    \E l2 \in Succ(l):
      /\ pc' = [pc EXCEPT ![p] = l2]
      /\ stack' = stack
      /\ shared' = [x \in SharedVars |-> IF x \in WShared(l) THEN CHOOSE v \in Values: TRUE ELSE shared[x]]
      /\ local' =
           [q \in P |->
              IF q = p
                 THEN [x \in LocalVars |-> IF x \in WLocal(l) THEN CHOOSE v \in Values: TRUE ELSE local[q][x]]
                 ELSE local[q]]
  ELSE IF Tag(l) = "Call" THEN
    LET ret == The(Succ(l)) IN
      /\ pc' = [pc EXCEPT ![p] = Callee(l)]
      /\ stack' = [stack EXCEPT ![p] = Append(stack[p], ret)]
      /\ shared' = [x \in SharedVars |-> IF x \in WShared(l) THEN CHOOSE v \in Values: TRUE ELSE shared[x]]
      /\ local' =
           [q \in P |->
              IF q = p
                 THEN [x \in LocalVars |-> IF x \in WLocal(l) THEN CHOOSE v \in Values: TRUE ELSE local[q][x]]
                 ELSE local[q]]
  ELSE IF Tag(l) = "Return" THEN
      /\ Len(stack[p]) > 0
      /\ pc' = [pc EXCEPT ![p] = Last(stack[p])]
      /\ stack' = [stack EXCEPT ![p] = SubSeq(stack[p], 1, Len(stack[p]) - 1)]
      /\ shared' = shared
      /\ local' = local
  ELSE
      FALSE

Next ==
  \E p \in P: ProcStep(p)

Spec ==
  (Init /\ [][Next]_vars)
  /\ CASE FairnessOption = "None"     -> TRUE
       [] FairnessOption = "WFProcs"  -> \A p \in P: WF_vars(ProcStep(p))
       [] FairnessOption = "WFNext"   -> WF_vars(Next)
       [] FairnessOption = "SFProcs"  -> \A p \in P: SF_vars(ProcStep(p))

Terminated ==
  \A p \in P: Tag(pc[p]) = "Done" /\ Len(stack[p]) = 0

Termination ==
  <> Terminated

=============================================================================