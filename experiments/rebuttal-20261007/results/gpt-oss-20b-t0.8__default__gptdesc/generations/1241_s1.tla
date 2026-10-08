MODULE PlusCalToTLA
EXTENDS Sequences, TLC

CONSTANTS PROC_IDS, FairnessOption, PROC_AST

VARIABLES LexSeq, ProcDone

(* Node type *)
TYPEDEF Node == [ kind : STRING, value : ANY ]

IsProc(node) ==
  /\ node.kind = "proc"
  /\ node.value # ""

TranslateProc(procNode) ==
  LET s == <<procNode.value>> IN s

NextAction(pid) ==
  /\ pid \in PROC_IDS
  /\ ~ProcDone[pid]
  /\ LexSeq' = LexSeq ^ TranslateProc(PROC_AST[pid])
  /\ ProcDone'[pid] = TRUE

Next == \/ \E pid \in PROC_IDS : NextAction(pid)

Init ==
  /\ LexSeq = <<>>
  /\ \A p \in PROC_IDS : ProcDone[p] = FALSE

TypeInv ==
  /\ LexSeq \in Seq(STRING)
  /\ ProcDone : [p \in PROC_IDS -> BOOLEAN]
  /\ PROC_AST : [p \in PROC_IDS -> Node]

ProcASTKindInv ==
  \A p \in PROC_IDS : IsProc(PROC_AST[p])

FairnessCond ==
  CASE FairnessOption = "NoFair" -> TRUE
       \/ FairnessOption = "WeakProc" ->
           \A pid \in PROC_IDS : WF_(NextAction(pid))
       \/ FairnessOption = "WeakNext" -> WF_(Next)
       \/ FairnessOption = "StrongProc" ->
           \A pid \in PROC_IDS : SF_(NextAction(pid))

Spec == Init /\ [][Next]_<<LexSeq, ProcDone>> 
          /\ TypeInv /\ ProcASTKindInv
          /\ FairnessCond
          /\ <> \A p \in PROC_IDS : ProcDone[p] = TRUE

END MODULE