---------------------------- MODULE LockHS ----------------------------
EXTENDS Integers, TLAPS

CONSTANT Procs

VARIABLES pc, h_turn, s

vars == <<pc, h_turn, s>>

-----------------------------------------------------------------------------
(* Type invariant for the extended specification *)
TypeOKHS == 
    /\ pc \in [Procs -> {"idle", "trying", "critical"}]
    /\ h_turn \in Procs \cup {0}
    /\ s \in [Procs -> 0..2]

(* Initial state *)
Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ h_turn = 0
    /\ s = [p \in Procs |-> 0]

(* Process p begins trying to enter critical section *)
(* Stuttering step 0: set flag (simulated) *)
Enter0(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 0
    /\ s' = [s EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ h_turn' = h_turn

(* Stuttering step 1: set turn *)
Enter1(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 1
    /\ s' = [s EXCEPT ![p] = 2]
    /\ h_turn' = p
    /\ pc' = pc

(* Stuttering step 2: complete entry to critical section *)
Enter2(p) ==
    /\ pc[p] = "trying"
    /\ s[p] = 2
    /\ \/ h_turn # p
       \/ \A q \in Procs \ {p} : pc[q] \in {"idle", "critical"}
    /\ s' = [s EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ h_turn' = h_turn

(* Process p exits critical section *)
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ s' = s
    /\ h_turn' = h_turn

(* Combined next state relation *)
Next ==
    \E p \in Procs :
        \/ Enter0(p)
        \/ Enter1(p)
        \/ Enter2(p)
        \/ Exit(p)

(* Specification with stuttering and history *)
SpecHS == Init /\ [][Next]_vars

(* Mutual exclusion invariant *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

(* Invariant for the HS specification *)
InvHS ==
    /\ TypeOKHS
    /\ MutualExclusion

(* Lock invariant - ensures mutual exclusion *)
LockInv == MutualExclusion

-----------------------------------------------------------------------------
(* Basic Lock specification without auxiliary variables *)

VARIABLES pc0

varsLock == <<pc0>>

InitLock ==
    pc0 = [p \in Procs |-> "idle"]

TryLock(p) ==
    /\ pc0[p] = "idle"
    /\ pc0' = [pc0 EXCEPT ![p] = "trying"]

EnterLock(p) ==
    /\ pc0[p] = "trying"
    /\ \A q \in Procs \ {p} : pc0[q] # "critical"
    /\ pc0' = [pc0 EXCEPT ![p] = "critical"]

ExitLock(p) ==
    /\ pc0[p] = "critical"
    /\ pc0' = [pc0 EXCEPT ![p] = "idle"]

NextLock ==
    \E p \in Procs :
        \/ TryLock(p)
        \/ EnterLock(p)
        \/ ExitLock(p)

Spec == InitLock /\ [][NextLock]_varsLock

-----------------------------------------------------------------------------
(* Peterson specification instantiation *)

PInit ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ h_turn \in Procs \cup {0}
    /\ s = [p \in Procs |-> 0]

PNext ==
    \E p \in Procs :
        \/ Enter0(p)
        \/ Enter1(p)
        \/ Enter2(p)
        \/ Exit(p)

PSpec == PInit /\ [][PNext]_vars /\ WF_vars(Next)

=============================================================================