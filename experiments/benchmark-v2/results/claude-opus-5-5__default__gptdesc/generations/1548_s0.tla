---------------------------- MODULE OneStepByzCons ----------------------------
(***************************************************************************)
(* Folklore one-step consensus with Byzantine faults, after Dobre and     *)
(* Suri (DSN 2006).                                                        *)
(*                                                                         *)
(*   N : number of processes                                               *)
(*   T : threshold parameter (upper bound on faults assumed by the code)   *)
(*   F : actual number of Byzantine processes tolerated in a run           *)
(*                                                                         *)
(* Process locations:                                                      *)
(*   V0, V1  : initial, with proposal 0 / 1                                *)
(*   S0, S1  : proposal has been broadcast                                 *)
(*   D0, D1  : decided 0 / 1 in one step                                   *)
(*   U0, U1  : not decided, adopted estimate 0 / 1 for underlying cons.    *)
(*   BYZ     : process has become Byzantine (faulty)                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME N > 3 * T /\ T >= F

Proc == 1 .. N

Locations == {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ"}
Decided   == {"D0", "D1"}
Final     == {"D0", "D1", "U0", "U1"}

VARIABLES
    nSnt0,    \* number of 0-messages sent by correct processes
    nSnt1,    \* number of 1-messages sent by correct processes
    nRcvd0,   \* nRcvd0[i]: number of 0-messages received by process i
    nRcvd1,   \* nRcvd1[i]: number of 1-messages received by process i
    nFaulty,  \* number of processes that have become faulty
    pc        \* pc[i]: location of process i

vars == << nSnt0, nSnt1, nRcvd0, nRcvd1, nFaulty, pc >>

Corr == { i \in Proc : pc[i] # "BYZ" }

TypeOK ==
    /\ nSnt0 \in 0 .. N
    /\ nSnt1 \in 0 .. N
    /\ nRcvd0 \in [Proc -> 0 .. N]
    /\ nRcvd1 \in [Proc -> 0 .. N]
    /\ nFaulty \in 0 .. F
    /\ pc \in [Proc -> Locations]

-----------------------------------------------------------------------------
(* Initial states *)

InitCommon ==
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nRcvd0 = [i \in Proc |-> 0]
    /\ nRcvd1 = [i \in Proc |-> 0]
    /\ nFaulty = 0

Init ==
    /\ InitCommon
    /\ pc \in [Proc -> {"V0", "V1"}]

\* All correct processes propose 0
Init0 ==
    /\ InitCommon
    /\ pc = [i \in Proc |-> "V0"]

\* All correct processes propose 1
Init1 ==
    /\ InitCommon
    /\ pc = [i \in Proc |-> "V1"]

-----------------------------------------------------------------------------
(* Actions *)

\* A process broadcasts its proposal
Propose(i) ==
    \/ /\ pc[i] = "V0"
       /\ pc' = [pc EXCEPT ![i] = "S0"]
       /\ nSnt0' = nSnt0 + 1
       /\ UNCHANGED << nSnt1, nRcvd0, nRcvd1, nFaulty >>
    \/ /\ pc[i] = "V1"
       /\ pc' = [pc EXCEPT ![i] = "S1"]
       /\ nSnt1' = nSnt1 + 1
       /\ UNCHANGED << nSnt0, nRcvd0, nRcvd1, nFaulty >>

\* A correct process receives one more message; Byzantine processes may
\* send messages carrying either value, hence the "+ nFaulty" bound.
Receive(i) ==
    /\ pc[i] \in {"V0", "V1", "S0", "S1"}
    /\ \/ /\ nRcvd0[i] < nSnt0 + nFaulty
          /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1]
          /\ UNCHANGED nRcvd1
       \/ /\ nRcvd1[i] < nSnt1 + nFaulty
          /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1]
          /\ UNCHANGED nRcvd0
    /\ UNCHANGED << nSnt0, nSnt1, nFaulty, pc >>

\* After receiving N - T messages, a process either decides (if N - T of
\* them carry the same value) or adopts an estimate.
Decide(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd0[i] + nRcvd1[i] >= N - T
    /\ \/ /\ nRcvd0[i] >= N - T
          /\ pc' = [pc EXCEPT ![i] = "D0"]
       \/ /\ nRcvd1[i] >= N - T
          /\ pc' = [pc EXCEPT ![i] = "D1"]
       \/ /\ nRcvd0[i] < N - T
          /\ nRcvd1[i] < N - T
          /\ nRcvd0[i] >= nRcvd1[i]
          /\ pc' = [pc EXCEPT ![i] = "U0"]
       \/ /\ nRcvd0[i] < N - T
          /\ nRcvd1[i] < N - T
          /\ nRcvd1[i] > nRcvd0[i]
          /\ pc' = [pc EXCEPT ![i] = "U1"]
    /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1, nFaulty >>

\* A process that has not yet sent anything becomes Byzantine
BecomeFaulty(i) ==
    /\ nFaulty < F
    /\ pc[i] \in {"V0", "V1"}
    /\ pc' = [pc EXCEPT ![i] = "BYZ"]
    /\ nFaulty' = nFaulty + 1
    /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

Step(i) ==
    \/ Propose(i)
    \/ Receive(i)
    \/ Decide(i)

MainStep == \E i \in Proc : Step(i)

Next ==
    \/ MainStep
    \/ \E i \in Proc : BecomeFaulty(i)

-----------------------------------------------------------------------------
(* Specifications *)

Spec  == Init  /\ [][Next]_vars /\ WF_vars(MainStep)
Spec0 == Init0 /\ [][Next]_vars /\ WF_vars(MainStep)
Spec1 == Init1 /\ [][Next]_vars /\ WF_vars(MainStep)

-----------------------------------------------------------------------------
(* Safety properties *)

\* No two correct processes decide differently
Agreement ==
    \A i, j \in Proc :
        (pc[i] = "D0") => (pc[j] # "D1")

\* Validity (check under Spec0): if all propose 0, nobody decides 1
Unforg0 == \A i \in Proc : pc[i] # "D1"

\* Validity (check under Spec1): if all propose 1, nobody decides 0
Unforg1 == \A i \in Proc : pc[i] # "D0"

\* A process that decides v forces every other correct process that leaves
\* the one-step round to keep v as its estimate
Consistency ==
    \A i, j \in Proc :
        /\ (pc[i] = "D0") => (pc[j] \notin {"D1", "U1"})
        /\ (pc[i] = "D1") => (pc[j] \notin {"D0", "U0"})

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every correct process eventually finishes the one-step round
Termination ==
    <>(\A i \in Proc : pc[i] \in Final \cup {"BYZ"})

\* If all propose 0 (resp. 1), every correct process eventually decides
\* 0 (resp. 1) in one step (check under Spec0 / Spec1, with F = 0)
OneStep0 == <>(\A i \in Proc : pc[i] \in {"D0", "BYZ"})
OneStep1 == <>(\A i \in Proc : pc[i] \in {"D1", "BYZ"})

=============================================================================