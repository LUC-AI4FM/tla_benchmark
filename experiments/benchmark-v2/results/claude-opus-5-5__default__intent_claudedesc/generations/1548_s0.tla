------------------------------ MODULE c1cs ------------------------------
(***************************************************************************)
(* One-step Byzantine consensus: Algorithm 2 from Dobre and Suri,          *)
(* "One-step consensus with zero-degradation", DSN 2006.                   *)
(*                                                                         *)
(* There are N processes. At most F of them are Byzantine, with F <= T     *)
(* and N > 3T. Each correct process proposes 0 or 1 and broadcasts its     *)
(* value. Once it has received at least N-T messages, it decides:          *)
(*   - 0 if it received at least N-T "0" messages;                         *)
(*   - 1 if it received at least N-T "1" messages;                         *)
(*   - otherwise it keeps its own proposal (states U0 / U1).               *)
(* Messages from correct and faulty senders are counted separately.        *)
(*                                                                         *)
(* Process states:                                                         *)
(*   V0, V1   initial value, not yet broadcast                             *)
(*   S0, S1   value broadcast                                              *)
(*   D0, D1   decided                                                      *)
(*   U0, U1   neither threshold met; keeps its own proposal                *)
(*   BYZ      Byzantine                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0

VARIABLES
  nSnt0,    \* number of 0-messages sent by correct processes
  nSnt1,    \* number of 1-messages sent by correct processes
  nSnt0F,   \* number of 0-messages sent by faulty processes
  nSnt1F,   \* number of 1-messages sent by faulty processes
  nFaulty,  \* number of faulty processes
  pc,       \* control state of each process
  nRcvd0,   \* number of 0-messages received by each process
  nRcvd1    \* number of 1-messages received by each process

vars == << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd0, nRcvd1 >>

Proc == 1 .. N

Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

Correct(i) == pc[i] # "BYZ"

Init ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* Initial states where every process proposes 0, or every process proposes 1.
Init0 ==
  /\ nSnt0 = 0 /\ nSnt1 = 0 /\ nSnt0F = 0 /\ nSnt1F = 0 /\ nFaulty = 0
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

Init1 ==
  /\ nSnt0 = 0 /\ nSnt1 = 0 /\ nSnt0F = 0 /\ nSnt1F = 0 /\ nFaulty = 0
  /\ pc = [ i \in Proc |-> "V1" ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

(***************************************************************************)
(* A process becomes Byzantine, up to the bound F. A Byzantine process     *)
(* may send arbitrary messages, so it may contribute both a 0-message and  *)
(* a 1-message.                                                            *)
(***************************************************************************)
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ nSnt0F' = nSnt0F + 1
  /\ nSnt1F' = nSnt1F + 1
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

\* A correct process broadcasts its initial value.
Propose(i) ==
  \/ /\ pc[i] = "V0"
     /\ pc' = [ pc EXCEPT ![i] = "S0" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[i] = "V1"
     /\ pc' = [ pc EXCEPT ![i] = "S1" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

\* A correct process receives one more message, from either a correct or a faulty sender.
Receive(i) ==
  /\ pc[i] # "BYZ"
  /\ \/ /\ nRcvd0[i] < nSnt0 + nSnt0F
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
        /\ UNCHANGED nRcvd1
     \/ /\ nRcvd1[i] < nSnt1 + nSnt1F
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
        /\ UNCHANGED nRcvd0
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc >>

\* A correct process decides after receiving at least N - T messages.
Decide(i) ==
  /\ pc[i] \in { "S0", "S1" }
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ pc[i] = "S0"
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ pc[i] = "S1"
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

CorrectStep(i) == Propose(i) \/ Receive(i) \/ Decide(i)

Next ==
  \/ \E i \in Proc : Faulty(i) \/ CorrectStep(i)
  \/ UNCHANGED vars

\* Weak fairness ensures that correct processes eventually propose, receive, and decide.
Fairness ==
  /\ WF_vars(\E i \in Proc : CorrectStep(i))
  /\ \A i \in Proc : WF_vars(Propose(i)) /\ WF_vars(Decide(i)) /\ WF_vars(Receive(i))

Spec  == Init  /\ [][Next]_vars /\ Fairness
Spec0 == Init0 /\ [][Next]_vars /\ Fairness
Spec1 == Init1 /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Type safety                                                             *)
(***************************************************************************)
TypeOK ==
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nSnt0F \in 0 .. F
  /\ nSnt1F \in 0 .. F
  /\ nFaulty \in 0 .. F
  /\ pc \in [ Proc -> Status ]
  /\ nRcvd0 \in [ Proc -> 0 .. (N + F) ]
  /\ nRcvd1 \in [ Proc -> 0 .. (N + F) ]

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* (1) All correct processes propose 0: no correct process ever decides 1
\*     or ends undecided with value 1.
OneStep0_Ltl ==
  (\A i \in Proc : pc[i] = "V0")
    => [](\A i \in Proc : pc[i] # "D1" /\ pc[i] # "U1")

\* (2) All correct processes propose 1: no correct process ever decides 0
\*     or ends undecided with value 0, and every correct process eventually
\*     settles on 1.
OneStep1_Ltl ==
  (\A i \in Proc : pc[i] = "V1")
    => /\ [](\A i \in Proc : pc[i] # "D0" /\ pc[i] # "U0")
       /\ <>(\A i \in Proc : pc[i] \in { "D1", "U1", "BYZ" })

\* Invariant forms of properties (1) and (2), for use with Spec0 and Spec1.
Inv0 == \A i \in Proc : pc[i] # "D1" /\ pc[i] # "U1"
Inv1 == \A i \in Proc : pc[i] # "D0" /\ pc[i] # "U0"

\* (3) All-ones initialization: every process eventually decides 1.
\*     Processes that become Byzantine are exempt.
Termination1 ==
  <>(\A i \in Proc : pc[i] \in { "D1", "U1", "BYZ" })

\* General termination: every correct process eventually settles.
Termination ==
  <>(\A i \in Proc : pc[i] \in { "D0", "D1", "U0", "U1", "BYZ" })

THEOREM Spec => []TypeOK
THEOREM Spec => OneStep0_Ltl
THEOREM Spec => OneStep1_Ltl
THEOREM Spec0 => []Inv0
THEOREM Spec1 => []Inv1
THEOREM Spec1 => Termination1
=============================================================================