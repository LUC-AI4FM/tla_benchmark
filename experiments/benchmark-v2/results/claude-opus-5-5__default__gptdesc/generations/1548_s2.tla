------------------------------ MODULE cf1s ------------------------------
(***************************************************************************)
(* Folklore one-step consensus algorithm with Byzantine faults,           *)
(* as described by Dobre and Suri (DSN 2006).                             *)
(*                                                                         *)
(* N processes, at most F of them Byzantine, T is the threshold parameter  *)
(* (F <= T, N > 3T). The model counts sent and received messages, tracks   *)
(* the number of faulty processes and the local state of each process.    *)
(*                                                                         *)
(* Local states:                                                           *)
(*   V0, V1 : initial state with proposal 0 / 1                            *)
(*   EX     : proposal sent, waiting for messages                          *)
(*   D0, D1 : decided 0 / 1 in one step                                    *)
(*   U0, U1 : did not decide, call the underlying consensus with 0 / 1     *)
(*   BYZ    : Byzantine (faulty)                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES pc,      \* local state of every process
          nSnt0,   \* number of messages with value 0 sent by correct processes
          nSnt1,   \* number of messages with value 1 sent by correct processes
          nSnt0F,  \* number of messages with value 0 sent by faulty processes
          nSnt1F,  \* number of messages with value 1 sent by faulty processes
          nFaulty, \* number of faulty processes
          nRcvd0,  \* number of 0-messages received by each process
          nRcvd1   \* number of 1-messages received by each process

ASSUME NTF == /\ N \in Nat /\ T \in Nat /\ F \in Nat
              /\ N > 3 * T
              /\ T >= F
              /\ F >= 0

Proc   == 1 .. N
Status == { "V0", "V1", "EX", "D0", "D1", "U0", "U1", "BYZ" }

vars == << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

(***************************************************************************)
(* Initial states                                                          *)
(***************************************************************************)
InitCommon ==
  /\ nSnt0   = 0
  /\ nSnt1   = 0
  /\ nSnt0F  = 0
  /\ nSnt1F  = 0
  /\ nFaulty = 0
  /\ nRcvd0  = [ i \in Proc |-> 0 ]
  /\ nRcvd1  = [ i \in Proc |-> 0 ]

Init  == /\ pc \in [ Proc -> { "V0", "V1" } ]
         /\ InitCommon

\* all processes propose 0
Init0 == /\ pc = [ i \in Proc |-> "V0" ]
         /\ InitCommon

\* all processes propose 1
Init1 == /\ pc = [ i \in Proc |-> "V1" ]
         /\ InitCommon

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A correct process broadcasts its proposal.
Propose(self) ==
  \/ /\ pc[self] = "V0"
     /\ pc' = [ pc EXCEPT ![self] = "EX" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[self] = "V1"
     /\ pc' = [ pc EXCEPT ![self] = "EX" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

\* A correct process receives one more message (0 or 1).
Receive(self) ==
  /\ pc[self] # "BYZ"
  /\ \/ /\ nRcvd0[self] < nSnt0 + nSnt0F
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![self] = nRcvd0[self] + 1 ]
        /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd1 >>
     \/ /\ nRcvd1[self] < nSnt1 + nSnt1F
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![self] = nRcvd1[self] + 1 ]
        /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0 >>

\* After receiving N - T messages, a correct process either decides in one
\* step, or falls back to the underlying consensus with a chosen estimate.
Decide(self) ==
  /\ pc[self] = "EX"
  /\ nRcvd0[self] + nRcvd1[self] >= N - T
  /\ \/ /\ nRcvd0[self] >= N - T
        /\ pc' = [ pc EXCEPT ![self] = "D0" ]
     \/ /\ nRcvd1[self] >= N - T
        /\ pc' = [ pc EXCEPT ![self] = "D1" ]
     \/ /\ nRcvd0[self] < N - T
        /\ nRcvd1[self] < N - T
        /\ nRcvd0[self] >= N - 2 * T
        /\ pc' = [ pc EXCEPT ![self] = "U0" ]
     \/ /\ nRcvd0[self] < N - T
        /\ nRcvd1[self] < N - T
        /\ nRcvd0[self] < N - 2 * T
        /\ pc' = [ pc EXCEPT ![self] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

\* A process that has not yet sent becomes Byzantine; it may send both 0 and 1.
Faulty(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ nFaulty < F
  /\ pc' = [ pc EXCEPT ![self] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ nSnt0F' = nSnt0F + 1
  /\ nSnt1F' = nSnt1F + 1
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

\* The main step of a correct process.
Step(self) == Propose(self) \/ Receive(self) \/ Decide(self)

Next ==
  \/ \E self \in Proc : Step(self)
  \/ \E self \in Proc : Faulty(self)
  \/ UNCHANGED vars

Spec  == Init  /\ [][Next]_vars /\ \A self \in Proc : WF_vars(Step(self))
Spec0 == Init0 /\ [][Next]_vars /\ \A self \in Proc : WF_vars(Step(self))
Spec1 == Init1 /\ [][Next]_vars /\ \A self \in Proc : WF_vars(Step(self))

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ nSnt0 \in 0 .. N /\ nSnt1 \in 0 .. N
  /\ nSnt0F \in 0 .. N /\ nSnt1F \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ nRcvd0 \in [ Proc -> 0 .. N ]
  /\ nRcvd1 \in [ Proc -> 0 .. N ]

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* No two correct processes decide differently in one step.
Agreement ==
  ~ ( \E i, j \in Proc : pc[i] = "D0" /\ pc[j] = "D1" )

\* If some correct process decides v in one step, no correct process
\* falls back to the underlying consensus with the other value.
AgreementUnderlying ==
  /\ (\E i \in Proc : pc[i] = "D0") => (\A j \in Proc : pc[j] # "U1")
  /\ (\E i \in Proc : pc[i] = "D1") => (\A j \in Proc : pc[j] # "U0")

SafetyInv == TypeOK /\ Agreement /\ AgreementUnderlying

\* Validity: if all propose 0 (resp. 1), nobody decides or estimates 1 (resp. 0).
Validity0 ==
  (\A i \in Proc : pc[i] = "V0") => [](\A i \in Proc : pc[i] \notin { "D1", "U1" })
Validity1 ==
  (\A i \in Proc : pc[i] = "V1") => [](\A i \in Proc : pc[i] \notin { "D0", "U0" })

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Every correct process eventually decides or goes to the underlying consensus.
Termination ==
  <>(\A i \in Proc : pc[i] \in { "D0", "D1", "U0", "U1", "BYZ" })

\* One-step decision: if all correct processes propose 0 (resp. 1),
\* then all correct processes eventually decide 0 (resp. 1) in one step.
OneStep0 ==
  (\A i \in Proc : pc[i] = "V0") => <>(\A i \in Proc : pc[i] \in { "D0", "BYZ" })
OneStep1 ==
  (\A i \in Proc : pc[i] = "V1") => <>(\A i \in Proc : pc[i] \in { "D1", "BYZ" })

THEOREM Spec => []SafetyInv
THEOREM Spec => Validity0 /\ Validity1 /\ Termination /\ OneStep0 /\ OneStep1

=============================================================================