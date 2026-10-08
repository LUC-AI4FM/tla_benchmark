------------------------------ MODULE TerminationDetection ------------------------------

EXTENDS Naturals

CONSTANTS 
    N,        \* Number of processes (finite, > 0)
    MaxMsg    \* Per-destination bound on in-transit messages for model checking

ASSUME /\ N \in Nat /\ N > 0
       /\ MaxMsg \in Nat

(*
Processes are arranged in an abstract logical topology of size N (e.g., a ring).
This model allows sends to any process; topology does not constrain behavior here.
*)

Proc == 1..N

VARIABLES 
    active,    \* [Proc -> BOOLEAN]: TRUE iff process is active
    msgs,      \* [Proc -> 0..MaxMsg]: number of in-transit messages destined to each process
    detected   \* BOOLEAN: global predicate set TRUE when termination is detected

vars == << active, msgs, detected >>

TypeOK ==
    /\ active \in [Proc -> BOOLEAN]
    /\ msgs \in [Proc -> 0..MaxMsg]
    /\ detected \in BOOLEAN

Terminated ==
    /\ \A p \in Proc: ~active[p]
    /\ \A p \in Proc: msgs[p] = 0

Init ==
    /\ TypeOK
    /\ detected = FALSE

Send(p, q) ==
    /\ p \in Proc /\ q \in Proc
    /\ active[p]
    /\ msgs[q] < MaxMsg
    /\ msgs' = [msgs EXCEPT ![q] = @ + 1]
    /\ UNCHANGED <<active, detected>>

Receive(q) ==
    /\ q \in Proc
    /\ msgs[q] > 0
    /\ msgs' = [msgs EXCEPT ![q] = @ - 1]
    /\ active' = [active EXCEPT ![q] = TRUE]
    /\ UNCHANGED detected

Deactivate(p) ==
    /\ p \in Proc
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<msgs, detected>>

Detect ==
    /\ Terminated
    /\ ~detected
    /\ detected' = TRUE
    /\ UNCHANGED <<active, msgs>>

Next ==
    \/ (\E p \in Proc: \E q \in Proc: Send(p, q))
    \/ (\E q \in Proc: Receive(q))
    \/ (\E p \in Proc: Deactivate(p))
    \/ Detect

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Detect)

(*
Safety invariants
*)
TypeInvariant == []TypeOK

DetectionSafety == [](detected => Terminated)

(*
Quiescence/Stability: once globally terminated, no action can revive a process
or reintroduce messages.
*)
Quiescence == [](Terminated => UNCHANGED <<active, msgs>>)

(*
Liveness: if the system reaches a state of global termination,
eventually the detector will set 'detected' to TRUE (under WF on Detect).
*)
EventualDetection == [] (Terminated => <> detected)

=============================================================================