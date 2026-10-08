--------------------------- MODULE GlobalNamingTranslate ----------------------------
EXTENDS Naturals, Sequences

CONSTANT FairnessOption \* One of {"None", "WeakProc", "WeakNext", "StrongProc"}

VARIABLES
   ast,
   labels,
   subscriptMap,
   initState,
   nextAction,
   terminationFlag

(* Abstract syntax tree types *)
Node == [type : String, fields : Seq(Any)]
Expr == Node
Stmt == Node
Nodes == {n \in Node | TRUE}

IsExpr(n) == n.type = "expr"
IsStmt(n) == n.type = "stmt"

ExplodeLabels(stms) ==
  stms

TranslateCalls(stms) ==
  stms

AddSubscripts(stms) ==
  stms

BuildInit(ast) ==
  [value |-> ast]

BuildNext(ast, subscriptMap) ==
  [value |-> ast] \* placeholder

Init ==
  /\ ast \in Nodes
  /\ labels \in Seq(Stmt)
  /\ subscriptMap \in [Any -> Any]
  /\ initState = BuildInit(ast)
  /\ nextAction = <<>>
  /\ terminationFlag = FALSE

Next ==
  \/ (* process action *)
     LET newState == TranslateCalls(AddSubscripts(ExplodeLabels(labels))) IN
        /\ nextAction' = newState
        /\ UNCHANGED <<ast, labels, subscriptMap, initState, terminationFlag>>
  \/ (* terminate *)
     /\ terminationFlag' = TRUE
     /\ UNCHANGED <<ast, labels, subscriptMap, initState, nextAction>>

LabelsConsistent ==
  \A s \in labels : IsStmt(s)

SpecBase ==
  Init /\ [][Next] /\ LabelsConsistent

FairSpec ==
  IF FairnessOption = "None" THEN SpecBase
  ELSEIF FairnessOption = "WeakProc" THEN SpecBase /\ WF_vars nextAction
  ELSEIF FairnessOption = "WeakNext" THEN SpecBase /\ WF_vars Next
  ELSE (* StrongProc *)
     SpecBase /\ SC_vars nextAction

Termination ==
  <> terminationFlag

Spec == FairSpec /\ Termination
=============================================================================