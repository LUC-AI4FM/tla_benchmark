----------------------------- MODULE OneStepByzConsensus -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  N, \* number of processes
  F, \* max number of Byzantine faults tolerated
  T  \* decision threshold

ASSUME /\ N \in Nat /\ N >= 1
       /\ F \in Nat /\ F >= 0 /\ F < N
       /\ T \in Nat /\ T >= 1
       /\ F < T
       /\ T <= N - F

(*
  Processes and values
*)
P == 1..N
Values == {0, 1}
MsgVals == Values \cup {"NoMsg"}

(*
  State variables
*)
VARIABLES
  mode,        \* "All0" or "All1" initial pattern for proposals
  proposal,    \* function P -> {0,1}
  faulty,      \* set of faulty processes
  state,       \* function P -> {"idle","sent","decided","faulty"}
  sent,        \* function P -> BOOLEAN, has process sent its one-step message
  sentVal,     \* function P -> (P -> MsgVals), value sent by s to r (or "NoMsg")
  received,    \* function P -> (P -> BOOLEAN), has r received from s
  numSent,     \* function P -> Nat, number of non-"NoMsg" messages process sent (fanout)
  numRecv,     \* function P -> Nat, number of messages received by process
  recvCount,   \* function P -> (Values -> Nat), per-receiver counts of 0s and 1s
  decided,     \* function P -> BOOLEAN
  decision     \* function P -> Values (meaningful when decided[p] = TRUE)

vars == << mode, proposal, faulty, state, sent, sentVal, received, numSent, numRecv, recvCount, decided, decision >>

Correct == P \ faulty

(*
  Typing and structural invariants
*)
TypeOK ==
  /\ mode \in {"All0","All1"}
  /\ proposal \in [P -> Values]
  /\ faulty \subseteq P
  /\ state \in [P -> {"idle","sent","decided","faulty"}]
  /\ sent \in [P -> BOOLEAN]
  /\ sentVal \in [P -> [P -> MsgVals]]
  /\ received \in [P -> [P -> BOOLEAN]]
  /\ numSent \in [P -> Nat]
  /\ numRecv \in [P -> Nat]
  /\ recvCount \in [P -> [Values -> Nat]]
  /\ decided \in [P -> BOOLEAN]
  /\ decision \in [P -> Values]

CountConsistent ==
  /\ \A p \in P: numSent[p] = Cardinality({ r \in P: sentVal[p][r] \in Values })
  /\ \A r \in P: numRecv[r] = Cardinality({ s \in P: received[r][s] })
  /\ \A r \in P: numRecv[r] = recvCount[r][0] + recvCount[r][1]

FaultBound == Cardinality(faulty) <= F

(*
  Initial states: all-0 or all-1 proposals, no faults, no messages exchanged
*)
Init ==
  /\ mode \in {"All0","All1"}
  /\ proposal = [p \in P |-> IF mode = "All0" THEN 0 ELSE 1]
  /\ faulty = {}
  /\ state = [p \in P |-> "idle"]
  /\ sent = [p \in P |-> FALSE]
  /\ sentVal = [s \in P |-> [r \in P |-> "NoMsg"]]
  /\ received = [r \in P |-> [s \in P |-> FALSE]]
  /\ numSent = [p \in P |-> 0]
  /\ numRecv = [p \in P |-> 0]
  /\ recvCount = [r \in P |-> [v \in Values |-> 0]]
  /\ decided = [p \in P |-> FALSE]
  /\ decision = [p \in P |-> 0]
  /\ TypeOK
  /\ CountConsistent
  /\ FaultBound

(*
  Actions
*)

BecomeFaulty(p) ==
  /\ p \in P \ faulty
  /\ Cardinality(faulty) < F
  /\ faulty' = faulty \cup {p}
  /\ state' = [state EXCEPT ![p] = "faulty"]
  /\ UNCHANGED << mode, proposal, sent, sentVal, received, numSent, numRecv, recvCount, decided, decision >>

SendCorrect(p) ==
  /\ p \in P \ faulty
  /\ sent[p] = FALSE
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ state' = [state EXCEPT ![p] = "sent"]
  /\ sentVal' = [sentVal EXCEPT ![p] = [r \in P |-> proposal[p]]]
  /\ numSent' = [numSent EXCEPT ![p] = N]
  /\ UNCHANGED << mode, proposal, faulty, received, numRecv, recvCount, decided, decision >>

SendFaulty(p) ==
  /\ p \in faulty
  /\ sent[p] = FALSE
  /\ \E m \in [P -> MsgVals]:
        /\ sent' = [sent EXCEPT ![p] = TRUE]
        /\ state' = [state EXCEPT ![p] = "faulty"]
        /\ sentVal' = [sentVal EXCEPT ![p] = m]
        /\ numSent' = [numSent EXCEPT ![p] = Cardinality({ r \in P: m[r] \in Values })]
        /\ UNCHANGED << mode, proposal, faulty, received, numRecv, recvCount, decided, decision >>

Receive(r, s) ==
  /\ r \in P /\ s \in P
  /\ received[r][s] = FALSE
  /\ sent[s] = TRUE
  /\ sentVal[s][r] \in Values
  /\ LET v == sentVal[s][r] IN
       /\ received' = [received EXCEPT ![r][s] = TRUE]
       /\ numRecv' = [numRecv EXCEPT ![r] = @ + 1]
       /\ recvCount' = [recvCount EXCEPT ![r][v] = @ + 1]
       /\ UNCHANGED << mode, proposal, faulty, state, sent, sentVal, numSent, decided, decision >>

Decide(r) ==
  /\ r \in P \ faulty
  /\ decided[r] = FALSE
  /\ \E v \in Values: recvCount[r][v] >= T
  /\ LET v == CHOOSE x \in Values: recvCount[r][x] >= T IN
       /\ decided' = [decided EXCEPT ![r] = TRUE]
       /\ decision' = [decision EXCEPT ![r] = v]
       /\ state' = [state EXCEPT ![r] = "decided"]
       /\ UNCHANGED << mode, proposal, faulty, sent, sentVal, received, numSent, numRecv, recvCount >>

(*
  System step: main operational actions (excluding fault introduction)
*)
Step ==
  \/ \E p \in P: SendCorrect(p)
  \/ \E p \in P: SendFaulty(p)
  \/ \E r \in P: \E s \in P: Receive(r, s)
  \/ \E r \in P: Decide(r)

Next ==
  Step
  \/ \E p \in P: BecomeFaulty(p)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Step)

(*
  Safety properties
*)
AgreementInv ==
  \A p \in P: \A q \in P:
    ((p \in Correct) /\ (q \in Correct) /\ decided[p] /\ decided[q])
      => decision[p] = decision[q]

ThresholdSoundnessInv ==
  \A r \in P: decided[r] => recvCount[r][decision[r]] >= T

Validity0 ==
  []( (mode = "All0") => (\A r \in P: (r \in Correct /\ decided[r]) => decision[r] = 0) )

Validity1 ==
  []( (mode = "All1") => (\A r \in P: (r \in Correct /\ decided[r]) => decision[r] = 1) )

NumBoundsInv ==
  /\ \A p \in P: numSent[p] <= N
  /\ \A r \in P: numRecv[r] <= N

StructuralInv == TypeOK /\ CountConsistent /\ FaultBound /\ NumBoundsInv

Safety == AgreementInv /\ ThresholdSoundnessInv /\ Validity0 /\ Validity1 /\ StructuralInv

(*
  Liveness property: eventual decision of all correct processes
  (under the threshold assumptions and weak fairness on the main step)
*)
Termination ==
  <>(\A r \in P: (r \in Correct) => decided[r])

=============================================================================