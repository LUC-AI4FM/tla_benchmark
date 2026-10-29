------------------------------ MODULE c1cs ------------------------------
(***************************************************************************)
(* One-step Byzantine consensus: Algorithm 2 from Dobre and Suri (2006).   *)
(* N processes, at most T Byzantine faults tolerated by the algorithm and  *)
(* at most F actually faulty processes, with N > 3T >= 3F >= 0.            *)
(* Messages are not tracked individually. Aggregate counters are used.     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES nSnt0,   \* messages with value 0 sent by correct processes
          nSnt1,   \* messages with value 1 sent by correct processes
          nSnt0F,  \* messages with value 0 injected by faulty processes
          nSnt1F,  \* messages with value 1 injected by faulty processes
          nFaulty, \* number of faulty processes
          pc,      \* program counter of each process
          nRcvd0,  \* number of 0-messages received by each process
          nRcvd1   \* number of 1-messages received by each process

ASSUME NTF == /\ N \in Nat /\ T \in Nat /\ F \in Nat
              /\ N > 3 * T
              /\ T >= F
              /\ F >= 0

Proc   == 1 .. N
Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

vars == << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd0, nRcvd1 >>

TypeOK ==
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nSnt0F \in 0 .. N
  /\ nSnt1F \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ pc \in [ Proc -> Status ]
  /\ nRcvd0 \in [ Proc -> 0 .. (2 * N) ]
  /\ nRcvd1 \in [ Proc -> 0 .. (2 * N) ]

Init ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

(* A correct process broadcasts its initial value. *)
Propose(i) ==
  \/ /\ pc[i] = "V0"
     /\ pc' = [ pc EXCEPT ![i] = "S0" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[i] = "V1"
     /\ pc' = [ pc EXCEPT ![i] = "S1" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

(* A process receives one more message, bounded by the messages sent. *)
Receive(i) ==
  /\ pc[i] # "BYZ"
  /\ \/ /\ nRcvd0[i] < nSnt0 + nSnt0F
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
        /\ UNCHANGED nRcvd1
     \/ /\ nRcvd1[i] < nSnt1 + nSnt1F
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
        /\ UNCHANGED nRcvd0
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc >>

(* After receiving at least N - T messages, a process decides in one step  *)
(* or falls back to an undecided state.                                    *)
Decide(i) ==
  /\ pc[i] \in { "S0", "S1" }
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd0[i] >= nRcvd1[i]
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd1[i] > nRcvd0[i]
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

(* A non-Byzantine process becomes Byzantine. If it has not yet sent its   *)
(* value, its message is counted as injected by a faulty process.          *)
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ nSnt0F' = IF pc[i] = "V0" THEN nSnt0F + 1 ELSE nSnt0F
  /\ nSnt1F' = IF pc[i] = "V1" THEN nSnt1F + 1 ELSE nSnt1F
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

Next ==
  \E i \in Proc :
     \/ Propose(i)
     \/ Receive(i)
     \/ Decide(i)
     \/ Faulty(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in Proc : Propose(i))
  /\ WF_vars(\E i \in Proc : Receive(i))
  /\ WF_vars(\E i \in Proc : Decide(i))

(* If all processes propose 0, then no process ever reaches U0, U1 or D1. *)
OneStep0_Ltl ==
  (\A i \in Proc : pc[i] = "V0")
    => [](\A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1" /\ pc[i] # "D1")

(* If all processes propose 1, then eventually all processes are outside  *)
(* U0, U1 and D0.                                                          *)
OneStep1_Ltl ==
  (\A i \in Proc : pc[i] = "V1")
    => <>(\A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1" /\ pc[i] # "D0")

(* Every process eventually decides 1. *)
AllDecideOne == <>(\A i \in Proc : pc[i] = "D1")

THEOREM Spec => []TypeOK
THEOREM Spec => OneStep0_Ltl
THEOREM Spec => OneStep1_Ltl

=============================================================================