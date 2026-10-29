------------------------------ MODULE bosco ------------------------------
(***************************************************************************)
(* One-step Byzantine-tolerant consensus subprotocol (Bosco-style).        *)
(*                                                                         *)
(* Each correct process proposes a binary value, broadcasts exactly one    *)
(* vote for that value, collects votes from correct and Byzantine          *)
(* processes, and once it has at least N-T votes it either:                *)
(*   - decides 0 if it has at least N-T votes for 0,                       *)
(*   - decides 1 if it has at least N-T votes for 1,                       *)
(*   - otherwise moves to an "undecided" state that keeps its proposal.    *)
(*                                                                         *)
(* The state is kept as counters:                                          *)
(*   nSnt0, nSnt1   : votes sent by correct processes                      *)
(*   nSnt0F, nSnt1F : (possibly forged) votes injected by Byzantine ones   *)
(*   nRcvd0, nRcvd1 : per-process counts of votes received                 *)
(*   nByz           : number of processes that became Byzantine            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME NTF ==
    /\ N \in Nat /\ T \in Nat /\ F \in Nat
    /\ N > 3 * T
    /\ T >= F
    /\ N > 0

VARIABLES
    pc,        \* control state of each process
    proposal,  \* initial proposal of each process (ghost, fixed at Init)
    nSnt0,     \* number of 0-votes sent by correct processes
    nSnt1,     \* number of 1-votes sent by correct processes
    nSnt0F,    \* number of 0-votes sent by Byzantine processes
    nSnt1F,    \* number of 1-votes sent by Byzantine processes
    nRcvd0,    \* nRcvd0[p] : 0-votes received by process p
    nRcvd1,    \* nRcvd1[p] : 1-votes received by process p
    nByz       \* number of Byzantine processes

vars == << pc, proposal, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nByz >>

P == 1 .. N

Quorum == N - T

(* Control states:                                                         *)
(*   V0/V1 : has proposal 0/1, vote not yet sent                           *)
(*   S0/S1 : has sent its vote 0/1, collecting votes                       *)
(*   D0/D1 : decided 0/1                                                   *)
(*   U0/U1 : undecided, proposal 0/1 preserved                             *)
(*   BYZ   : Byzantine                                                     *)
States    == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }
Proposing == { "V0", "V1" }
Sent      == { "S0", "S1" }
Decided   == { "D0", "D1" }
Undecided == { "U0", "U1" }
Terminal  == Decided \cup Undecided

Correct == { p \in P : pc[p] # "BYZ" }

---------------------------------------------------------------------------

Init ==
    /\ proposal \in [P -> {0, 1}]
    /\ pc = [p \in P |-> IF proposal[p] = 0 THEN "V0" ELSE "V1"]
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nSnt0F = 0
    /\ nSnt1F = 0
    /\ nRcvd0 = [p \in P |-> 0]
    /\ nRcvd1 = [p \in P |-> 0]
    /\ nByz = 0

(* A process that has not yet broadcast its vote becomes Byzantine.        *)
BecomeByzantine(p) ==
    /\ nByz < F
    /\ pc[p] \in Proposing
    /\ pc' = [pc EXCEPT ![p] = "BYZ"]
    /\ nByz' = nByz + 1
    /\ UNCHANGED << proposal, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1 >>

(* A correct process broadcasts exactly one vote for its proposal.        *)
Send(p) ==
    \/ /\ pc[p] = "V0"
       /\ pc' = [pc EXCEPT ![p] = "S0"]
       /\ nSnt0' = nSnt0 + 1
       /\ UNCHANGED << proposal, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nByz >>
    \/ /\ pc[p] = "V1"
       /\ pc' = [pc EXCEPT ![p] = "S1"]
       /\ nSnt1' = nSnt1 + 1
       /\ UNCHANGED << proposal, nSnt0, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nByz >>

(* Byzantine processes may inject (forged / equivocating) votes; each     *)
(* Byzantine process can send at most one vote of each value.             *)
FaultySend0 ==
    /\ nSnt0F < nByz
    /\ nSnt0F' = nSnt0F + 1
    /\ UNCHANGED << pc, proposal, nSnt0, nSnt1, nSnt1F, nRcvd0, nRcvd1, nByz >>

FaultySend1 ==
    /\ nSnt1F < nByz
    /\ nSnt1F' = nSnt1F + 1
    /\ UNCHANGED << pc, proposal, nSnt0, nSnt1, nSnt0F, nRcvd0, nRcvd1, nByz >>

(* A correct process that has sent its vote receives one more vote.       *)
Receive0(p) ==
    /\ pc[p] \in Sent
    /\ nRcvd0[p] < nSnt0 + nSnt0F
    /\ nRcvd0' = [nRcvd0 EXCEPT ![p] = @ + 1]
    /\ UNCHANGED << pc, proposal, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd1, nByz >>

Receive1(p) ==
    /\ pc[p] \in Sent
    /\ nRcvd1[p] < nSnt1 + nSnt1F
    /\ nRcvd1' = [nRcvd1 EXCEPT ![p] = @ + 1]
    /\ UNCHANGED << pc, proposal, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nByz >>

(* Decision rule: requires at least N-T received votes.                   *)
Decide(p) ==
    /\ pc[p] \in Sent
    /\ nRcvd0[p] + nRcvd1[p] >= Quorum
    /\ pc' = [pc EXCEPT ![p] =
                 IF nRcvd0[p] >= Quorum THEN "D0"
                 ELSE IF nRcvd1[p] >= Quorum THEN "D1"
                 ELSE IF pc[p] = "S0" THEN "U0"
                 ELSE "U1"]
    /\ UNCHANGED << proposal, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nByz >>

Step(p) ==
    \/ BecomeByzantine(p)
    \/ Send(p)
    \/ Receive0(p)
    \/ Receive1(p)
    \/ Decide(p)

Next ==
    \/ \E p \in P : Step(p)
    \/ FaultySend0
    \/ FaultySend1
    \/ UNCHANGED vars   \* stuttering once everything has terminated

Fairness ==
    \A p \in P :
        /\ WF_vars(Send(p))
        /\ WF_vars(Receive0(p))
        /\ WF_vars(Receive1(p))
        /\ WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties                                                       *)
---------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [P -> States]
    /\ proposal \in [P -> {0, 1}]
    /\ nSnt0 \in 0 .. N
    /\ nSnt1 \in 0 .. N
    /\ nSnt0F \in 0 .. N
    /\ nSnt1F \in 0 .. N
    /\ nRcvd0 \in [P -> 0 .. N]
    /\ nRcvd1 \in [P -> 0 .. N]
    /\ nByz \in 0 .. N

(* No more than F processes become Byzantine, and counts stay in 0..N.    *)
Bounds ==
    /\ nByz <= F
    /\ Cardinality({ p \in P : pc[p] = "BYZ" }) = nByz
    /\ nSnt0F <= nByz /\ nSnt1F <= nByz
    /\ nSnt0 + nSnt1 + nByz <= N
    /\ nSnt0 + nSnt0F <= N
    /\ nSnt1 + nSnt1F <= N
    /\ \A p \in P :
        /\ nRcvd0[p] \in 0 .. N
        /\ nRcvd1[p] \in 0 .. N
        /\ nRcvd0[p] <= nSnt0 + nSnt0F
        /\ nRcvd1[p] <= nSnt1 + nSnt1F

(* If all non-faulty processes propose 0, no correct process decides 1.   *)
Validity0 ==
    (\A p \in Correct : proposal[p] = 0) => (\A p \in Correct : pc[p] # "D1")

(* If all non-faulty processes propose 1, no correct process decides 0.   *)
Validity1 ==
    (\A p \in Correct : proposal[p] = 1) => (\A p \in Correct : pc[p] # "D0")

(* Decisions are consistent with the vote thresholds.                     *)
DecisionConsistent ==
    \A p \in Correct :
        /\ pc[p] = "D0" => nRcvd0[p] >= Quorum
        /\ pc[p] = "D1" => nRcvd1[p] >= Quorum
        /\ pc[p] \in Terminal => nRcvd0[p] + nRcvd1[p] >= Quorum
        /\ pc[p] = "U0" => proposal[p] = 0
        /\ pc[p] = "U1" => proposal[p] = 1

Safety == TypeOK /\ Bounds /\ Validity0 /\ Validity1 /\ DecisionConsistent

THEOREM Spec => []Safety

---------------------------------------------------------------------------
(* Liveness properties (under weak fairness)                               *)
---------------------------------------------------------------------------

(* Every correct process eventually reaches a terminal state (a decision  *)
(* or the undecided state preserving its proposal).                       *)
Termination ==
    <>(\A p \in P : pc[p] \in Terminal \cup {"BYZ"})

(* Whenever a correct process can decide, it eventually does so.          *)
DecideProgress ==
    \A p \in P :
        (pc[p] \in Sent /\ nRcvd0[p] + nRcvd1[p] >= Quorum)
            ~> (pc[p] \in Terminal)

(* Each correct process that has sent its vote eventually collects at     *)
(* least N-T votes.                                                       *)
ReceiveProgress ==
    \A p \in P :
        (pc[p] \in Sent) ~> (nRcvd0[p] + nRcvd1[p] >= Quorum)

Liveness == Termination /\ DecideProgress /\ ReceiveProgress

THEOREM Spec => Liveness

=============================================================================