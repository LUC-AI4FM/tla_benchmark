---------------------------- MODULE LockHS ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT Procs

VARIABLES pc, h_turn, s

vars == <<pc, h_turn, s>>

-----------------------------------------------------------------------------

(* Initial state *)
Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ h_turn = CHOOSE p \in Procs : TRUE
    /\ s = [p \in Procs |-> 0]

(* Type invariant with history and stuttering variables *)
TypeOKHS ==
    /\ pc \in [Procs -> {"idle", "waiting", "cs"}]
    /\ h_turn \in Procs
    /\ s \in [Procs -> 0..3]

(* Process p requests to enter critical section *)
Request(p) ==
    /\ pc[p] = "idle"
    /\ s[p] = 0
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ h_turn' = p
    /\ s' = [s EXCEPT ![p] = 1]

(* Stuttering step 1 - mimics flag[p] := TRUE in Peterson *)
Stutter1(p) ==
    /\ pc[p] = "waiting"
    /\ s[p] = 1
    /\ s' = [s EXCEPT ![p] = 2]
    /\ pc' = pc
    /\ h_turn' = h_turn

(* Stuttering step 2 - mimics turn := other in Peterson *)
Stutter2(p) ==
    /\ pc[p] = "waiting"
    /\ s[p] = 2
    /\ s' = [s EXCEPT ![p] = 3]
    /\ pc' = pc
    /\ h_turn' = IF \E q \in Procs : q # p /\ pc[q] = "waiting" /\ s[q] >= 2
                 THEN CHOOSE q \in Procs : q # p /\ pc[q] = "waiting" /\ s[q] >= 2
                 ELSE h_turn

(* Process p enters critical section *)
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ s[p] = 3
    /\ \A q \in Procs \ {p} : pc[q] # "cs"
    /\ \/ h_turn = p
       \/ \A q \in Procs \ {p} : pc[q] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ s' = s
    /\ h_turn' = h_turn

(* Process p exits critical section *)
Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ h_turn' = h_turn

(* Next state relation *)
Next ==
    \E p \in Procs :
        \/ Request(p)
        \/ Stutter1(p)
        \/ Stutter2(p)
        \/ Enter(p)
        \/ Exit(p)

(* Specification with history and stuttering *)
SpecHS == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(* Mutual exclusion invariant *)
MutualExclusion ==
    \A p, q \in Procs : p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Invariant for the history/stuttering specification *)
InvHS ==
    /\ TypeOKHS
    /\ MutualExclusion

(* Lock invariant - core safety property *)
LockInv == MutualExclusion

-----------------------------------------------------------------------------

(* Original Lock specification without auxiliary variables *)

VARIABLES pc0

varsLock == <<pc0>>

InitLock ==
    pc0 = [p \in Procs |-> "idle"]

TypeOKLock ==
    pc0 \in [Procs -> {"idle", "waiting", "cs"}]

RequestLock(p) ==
    /\ pc0[p] = "idle"
    /\ pc0' = [pc0 EXCEPT ![p] = "waiting"]

EnterLock(p) ==
    /\ pc0[p] = "waiting"
    /\ \A q \in Procs \ {p} : pc0[q] # "cs"
    /\ pc0' = [pc0 EXCEPT ![p] = "cs"]

ExitLock(p) ==
    /\ pc0[p] = "cs"
    /\ pc0' = [pc0 EXCEPT ![p] = "idle"]

NextLock ==
    \E p \in Procs :
        \/ RequestLock(p)
        \/ EnterLock(p)
        \/ ExitLock(p)

Spec == InitLock /\ [][NextLock]_varsLock

-----------------------------------------------------------------------------

(* Peterson specification instantiation *)

(* Map from LockHS to Peterson's algorithm states *)
PetersonPC(p) ==
    CASE pc[p] = "idle" -> "idle"
      [] pc[p] = "waiting" /\ s[p] = 1 -> "a1"
      [] pc[p] = "waiting" /\ s[p] = 2 -> "a2"
      [] pc[p] = "waiting" /\ s[p] = 3 -> "a3"
      [] pc[p] = "cs" -> "cs"
      [] OTHER -> "idle"

PetersonFlag(p) ==
    pc[p] # "idle"

PetersonTurn ==
    h_turn

(* Peterson specification - instantiated with mappings from LockHS *)
PSpec ==
    /\ \A p \in Procs : PetersonPC(p) \in {"idle", "a1", "a2", "a3", "cs"}
    /\ \A p \in Procs : PetersonFlag(p) \in BOOLEAN
    /\ PetersonTurn \in Procs

=============================================================================