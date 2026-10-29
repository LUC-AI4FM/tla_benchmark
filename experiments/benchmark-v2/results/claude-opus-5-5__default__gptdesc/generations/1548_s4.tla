------------------------------ MODULE cf1s_folklore ------------------------------
(***************************************************************************)
(* The folklore one-step consensus algorithm with Byzantine faults, as     *)
(* described by Dobre and Suri (DSN 2006). The protocol uses a counting    *)
(* abstraction: it tracks how many messages correct and faulty processes   *)
(* have sent, how many messages each process has received, how many       *)
(* processes are faulty, and the local state of each process.             *)
(*                                                                         *)
(* Local states:                                                           *)
(*   V0, V1 : initial value 0 / 1, not yet proposed                        *)
(*   S0, S1 : proposed (sent) value 0 / 1                                  *)
(*   D0, D1 : decided value 0 / 1 (in one step)                            *)
(*   U0, U1 : did not decide, adopted value 0 / 1 for the fallback         *)
(*   BYZ    : the process is Byzantine (faulty)                            *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES nSnt0,    \* messages with value 0 sent by correct processes
          nSnt1,    \* messages with value 1 sent by correct processes
          nSnt0F,   \* messages with value 0 sent by faulty processes
          nSnt1F,   \* messages with value 1 sent by faulty processes
          nFaulty,  \* number of faulty processes
          pc,       \* program counters (local states)
          nRcvd0,   \* number of 0-messages received by each process
          nRcvd1    \* number of 1-messages received by each process

ASSUME NTF == /\ N \in Nat /\ T \in Nat /\ F \in Nat
              /\ N > 3 * T
              /\ T >= F
              /\ F >= 0

Proc   == 1 .. N
Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

vars == << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd0, nRcvd1 >>

(***************************************************************************)
(* Initial states                                                          *)
(***************************************************************************)
Init ==
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* All processes propose 0
Init0 ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* All processes propose 1
Init1 ==
  /\ pc = [ i \in Proc |-> "V1" ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A process becomes Byzantine. If it has not yet proposed, it may inject a
\* message with its value as a faulty message.
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ IF pc[i] = "V0" THEN nSnt0F' = nSnt0F + 1 ELSE nSnt0F' = nSnt0F
  /\ IF pc[i] = "V1" THEN nSnt1F' = nSnt1F + 1 ELSE nSnt1F' = nSnt1F
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

\* A correct process receives one more message (from correct or faulty senders).
Receive(i) ==
  /\ pc[i] # "BYZ"
  /\ \/ /\ nRcvd0[i] < nSnt0 + nSnt0F
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
        /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd1 >>
     \/ /\ nRcvd1[i] < nSnt1 + nSnt1F
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
        /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd0 >>

\* After receiving N - T messages, a correct process decides in one step or
\* adopts a value for the underlying (fallback) consensus.
Decide(i) ==
  /\ pc[i] \in { "S0", "S1" }
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd0[i] >= N - 2 * T
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd1[i] >= N - 2 * T
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
     \/ /\ nRcvd0[i] < N - 2 * T
        /\ nRcvd1[i] < N - 2 * T
        /\ pc[i] = "S0"
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - 2 * T
        /\ nRcvd1[i] < N - 2 * T
        /\ pc[i] = "S1"
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

\* The main (non-faulty) step
Step ==
  \E self \in Proc :
    \/ Receive(self)
    \/ Propose(self)
    \/ Decide(self)

Next ==
  \/ Step
  \/ \E self \in Proc : Faulty(self)
  \/ UNCHANGED vars

Spec  == Init  /\ [][Next]_vars /\ WF_vars(Step)
Spec0 == Init0 /\ [][Next]_vars /\ WF_vars(Step)
Spec1 == Init1 /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Invariants and properties                                               *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nSnt0F \in 0 .. N
  /\ nSnt1F \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ nRcvd0 \in [ Proc -> 0 .. N ]
  /\ nRcvd1 \in [ Proc -> 0 .. N ]

\* Agreement: no two processes decide differently in one step
Agreement ==
  \A i, j \in Proc : pc[i] = "D0" => pc[j] # "D1"

\* Agreement with the fallback: if someone decided v in one step,
\* no correct process adopts the other value
AgreementFallback ==
  /\ (\E i \in Proc : pc[i] = "D0") => (\A j \in Proc : pc[j] # "D1" /\ pc[j] # "U1")
  /\ (\E i \in Proc : pc[i] = "D1") => (\A j \in Proc : pc[j] # "D0" /\ pc[j] # "U0")

\* Validity: when all processes propose 0 (resp. 1), the other value is never chosen
Validity0 == [](\A i \in Proc : pc[i] # "D1" /\ pc[i] # "U1")
Validity1 == [](\A i \in Proc : pc[i] # "D0" /\ pc[i] # "U0")

\* One-step decision: if all correct processes propose the same value,
\* all correct processes eventually decide it in one step
OneStep0 == <>(\A i \in Proc : pc[i] = "D0" \/ pc[i] = "BYZ")
OneStep1 == <>(\A i \in Proc : pc[i] = "D1" \/ pc[i] = "BYZ")

\* Termination: every correct process eventually decides or falls back
Termination ==
  <>(\A i \in Proc : pc[i] \in { "D0", "D1", "U0", "U1", "BYZ" })

THEOREM Spec  => []TypeOK
THEOREM Spec  => []Agreement
THEOREM Spec  => []AgreementFallback
THEOREM Spec0 => Validity0
THEOREM Spec1 => Validity1
THEOREM Spec0 => OneStep0
THEOREM Spec1 => OneStep1
THEOREM Spec  => Termination

=============================================================================