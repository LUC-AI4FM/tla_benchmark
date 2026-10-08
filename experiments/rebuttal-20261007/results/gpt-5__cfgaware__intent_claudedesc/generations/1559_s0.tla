----------------------------- MODULE AugmentedLock -----------------------------

EXTENDS Naturals

(*
  Two-process universe and helper operators
*)
P == {0, 1}

Other(i) == IF i = 0 THEN 1 ELSE 0

PC == {"Idle", "Entry", "Crit", "Exit"}
Svals == {0, 1, 2, 3}
PLbl == {"idle", "e1", "e2", "e3", "crit", "exit"}

(***************************************************************************)
(* Original simple lock specification (coarse-grained entry)               *)
(***************************************************************************)

VARIABLES pc

Init ==
  pc = [i \in P |-> "Idle"]

IdleToEntry(i) ==
  /\ i \in P
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "Entry"]

EntryToCrit(i) ==
  /\ i \in P
  /\ pc[i] = "Entry"
  /\ \A j \in P: (j = i) \/ (pc[j] # "Crit")
  /\ pc' = [pc EXCEPT ![i] = "Crit"]

CritToExit(i) ==
  /\ i \in P
  /\ pc[i] = "Crit"
  /\ pc' = [pc EXCEPT ![i] = "Exit"]

ExitToIdle(i) ==
  /\ i \in P
  /\ pc[i] = "Exit"
  /\ pc' = [pc EXCEPT ![i] = "Idle"]

Next ==
  \E i \in P:
       IdleToEntry(i)
    \/ EntryToCrit(i)
    \/ CritToExit(i)
    \/ ExitToIdle(i)

LockInv ==
  \A i, j \in P : (i # j) => ~(pc[i] = "Crit" /\ pc[j] = "Crit")

Spec ==
  Init /\ [][Next]_pc

(***************************************************************************)
(* Augmented lock with History (hturn) and Stuttering (st) auxiliaries     *)
(* This is the refinement bridge between the simple lock and Peterson.     *)
(***************************************************************************)

VARIABLES hpc, st, hturn

InitHS ==
  /\ hpc = [i \in P |-> "Idle"]
  /\ st  = [i \in P |-> 0]
  /\ hturn = "None"

TypeOKHS ==
  /\ hpc \in [P -> PC]
  /\ st  \in [P -> Svals]
  /\ hturn \in (P \cup {"None"})

(*
  Entry in the base lock is expanded to three sub-steps using st[i]:
    - st[i] = 3 -> 2 : first internal sub-step; here we also record the turn assignment
                       in the history variable hturn := Other(i) (Peterson's "turn := j").
    - st[i] = 2 -> 1 : second internal sub-step (pure stuttering on original state).
    - st[i] = 1 -> 0 together with hpc[i]: "Entry" -> "Crit" when allowed (commit).
  Outside Entry, st[i] must be 0.
*)

HIdleToEntry(i) ==
  /\ i \in P
  /\ hpc[i] = "Idle"
  /\ hpc' = [hpc EXCEPT ![i] = "Entry"]
  /\ st'  = [st  EXCEPT ![i] = 3]
  /\ UNCHANGED hturn

HStutterDec(i) ==
  /\ i \in P
  /\ hpc[i] = "Entry"
  /\ st[i] \in {2, 3}
  /\ hpc' = hpc
  /\ st'  = [st EXCEPT ![i] = st[i] - 1]
  /\ hturn' = IF st[i] = 3 THEN Other(i) ELSE hturn

HCommitEntry(i) ==
  /\ i \in P
  /\ hpc[i] = "Entry"
  /\ st[i] = 1
  /\ \A j \in P: (j = i) \/ (hpc[j] # "Crit")
  /\ hpc' = [hpc EXCEPT ![i] = "Crit"]
  /\ st'  = [st  EXCEPT ![i] = 0]
  /\ UNCHANGED hturn

HCritToExit(i) ==
  /\ i \in P
  /\ hpc[i] = "Crit"
  /\ hpc' = [hpc EXCEPT ![i] = "Exit"]
  /\ UNCHANGED << st, hturn >>

HExitToIdle(i) ==
  /\ i \in P
  /\ hpc[i] = "Exit"
  /\ hpc' = [hpc EXCEPT ![i] = "Idle"]
  /\ UNCHANGED << st, hturn >>

NextHS ==
  \E i \in P:
       HIdleToEntry(i)
    \/ HStutterDec(i)
    \/ HCommitEntry(i)
    \/ HCritToExit(i)
    \/ HExitToIdle(i)

VarsHS == << hpc, st, hturn >>

(*
  Invariant connecting program counters, stuttering, and history "turn" ownership.
  - st[i] encodes where we are within the three-step Entry expansion.
  - When st[i] = 2 (i.e., immediately after the first internal sub-step 3->2),
    hturn equals the other process, recording the last "turn" assignment.
  - Outside Entry, st[i] = 0.
  - Mutual exclusion holds for hpc as well.
*)
InvHS ==
  /\ TypeOKHS
  /\ \A i \in P:
        (hpc[i] = "Entry") => st[i] \in {1,2,3}
  /\ \A i \in P:
        (hpc[i] # "Entry") => st[i] = 0
  /\ \A i \in P:
        (hpc[i] = "Entry" /\ st[i] = 2) => hturn = Other(i)
  /\ \A i, j \in P: (i # j) => ~(hpc[i] = "Crit" /\ hpc[j] = "Crit")

SpecHS ==
  InitHS /\ [][NextHS]_VarsHS

(***************************************************************************)
(* Peterson's two-process mutual exclusion algorithm (three-step entry)    *)
(***************************************************************************)

VARIABLES ppc, want, turn

PInit ==
  /\ ppc  = [i \in P |-> "idle"]
  /\ want = [i \in P |-> FALSE]
  /\ turn \in P

PBegin(i) ==
  /\ i \in P
  /\ ppc[i] = "idle"
  /\ ppc' = [ppc EXCEPT ![i] = "e1"]
  /\ UNCHANGED << want, turn >>

PE1(i) ==
  /\ i \in P
  /\ ppc[i] = "e1"
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ ppc'  = [ppc  EXCEPT ![i] = "e2"]
  /\ UNCHANGED turn

PE2(i) ==
  /\ i \in P
  /\ ppc[i] = "e2"
  /\ turn' = Other(i)
  /\ ppc'  = [ppc EXCEPT ![i] = "e3"]
  /\ UNCHANGED want

PE3(i) ==
  /\ i \in P
  /\ ppc[i] = "e3"
  /\ (~want[Other(i)] \/ turn = i)
  /\ ppc' = [ppc EXCEPT ![i] = "crit"]
  /\ UNCHANGED << want, turn >>

PCritToExit(i) ==
  /\ i \in P
  /\ ppc[i] = "crit"
  /\ ppc' = [ppc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << want, turn >>

PExitToIdle(i) ==
  /\ i \in P
  /\ ppc[i] = "exit"
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ ppc'  = [ppc  EXCEPT ![i] = "idle"]
  /\ UNCHANGED turn

PNext ==
  \E i \in P:
       PBegin(i)
    \/ PE1(i)
    \/ PE2(i)
    \/ PE3(i)
    \/ PCritToExit(i)
    \/ PExitToIdle(i)

PVars == << ppc, want, turn >>

PSpec ==
  PInit /\ [][PNext]_PVars

=============================================================================