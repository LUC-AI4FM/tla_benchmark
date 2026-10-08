MODULE TranslationSpec

EXTENDS Naturals, Sequences, TemporalOps

CONSTANTS
  N,
  FairnessOption,
  initAST

ASSUME FairnessOption \in {"NoFairness","WeakProcessFairness","StrongProcessFairness","WeakNextFairness"}

Symbol == {"Stmt", "Expr", "Call", "Return", "Goto", "Var"}
Node   == [type: Symbol, data: Any]
AST    == Seq(Node)

IsStmt(n)      == n.type = "Stmt"
IsExpr(n)      == n.type = "Expr"
IsCall(n)      == n.type = "Call"
IsReturn(n)    == n.type = "Return"
IsGoto(n)      == n.type = "Goto"
IsVar(n)       == n.type = "Var"

TranslateNode(n) ==
  IF IsCall(n) THEN
     [type |-> "Stmt", data |-> {"translated_call"}]
  ELSE
     n

Explode(node) ==
  node

BuildInitAST == initAST

ProcState == [locals : [x -> Nat]]
ProcIds   == 1..N

VARIABLES
  ast,
  procStates

vars == <<ast,procStates>>

Init ==
  /\ ast = BuildInitAST
  /\ procStates \in [ProcIds -> ProcState]
  /\ \A i \in ProcIds : procStates[i].locals.x = 0

ProcessStep(i) ==
  /\ i \in ProcIds
  /\ procStates' = [procStates EXCEPT ![i].locals.x = @ + 1]
  /\ UNCHANGED <<ast>>

Next == \E i \in ProcIds : ProcessStep(i)

AstInvariant ==
  ast = BuildInitAST

LocalVarNat(i) ==
  procStates[i].locals.x \in Nat

SafeInvariant ==
  \A i \in ProcIds : LocalVarNat(i)

Termination ==
  \A i \in ProcIds : <> (procStates[i].locals.x = 10)

FairnessCond ==
  IF FairnessOption = "NoFairness" THEN
     TRUE
  ELSE IF FairnessOption = "WeakProcessFairness" THEN
     \A i \in ProcIds : WF_M[ProcessStep(i)]
  ELSE IF FairnessOption = "StrongProcessFairness" THEN
     \A i \in ProcIds : SF_M[ProcessStep(i)]
  ELSE IF FairnessOption = "WeakNextFairness" THEN
     WF_M[Next]
  ELSE
     TRUE

Spec ==
  Init /\ [][Next]_vars /\ FairnessCond

END MODULE