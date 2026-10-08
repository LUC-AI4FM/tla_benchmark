---- MODULE MutexLock ----

CONSTANT Proc

ASSUME \E p1 \in Proc, p2 \in Proc : p1 # p2

VARIABLES lock, pc

LockVals == {"Unlocked", "Locked"}
CtrlStates == {"ncs", "try", "cs", "rel"}

TypeOK ==
  /\ lock \in LockVals
  /\ pc \in [Proc -> CtrlStates]

Init ==
  /\ lock = "Unlocked"
  /\ pc = [p \in Proc |-> "ncs"]

Holders == { p \in Proc : pc[p] \in {"cs", "rel"} }

LockInv == (lock = "Locked") <=> (Holders # {})

MutEx ==
  \A p, q \in Proc : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

NcsToTry(p) ==
  /\ p \in Proc
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED lock

TryToCs(p) ==
  /\ p \in Proc
  /\ pc[p] = "try"
  /\ lock = "Unlocked"
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ lock' = "Locked"

CsToRel(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "rel"]
  /\ UNCHANGED lock

RelToNcs(p) ==
  /\ p \in Proc
  /\ pc[p] = "rel"
  /\ pc' = [pc EXCEPT ![p] = "ncs"]
  /\ lock' = "Unlocked"

Next ==
  \E p \in Proc :
       NcsToTry(p)
    \/ TryToCs(p)
    \/ CsToRel(p)
    \/ RelToNcs(p)

Spec == Init /\ [][Next]_<<lock, pc>>

Inv == TypeOK /\ LockInv /\ MutEx

====