---- MODULE LockWithStuttering ----
EXTENDS Naturals, Sequences, Stuttering

CONSTANT Proc
CONSTANT Other

ASSUME /\ Proc \in SUBSET Nat
       /\ \A i \in Proc: Other(i) \in Proc
       /\ \A i \in Proc: Other(Other(i)) = i
       /\ \A i \in Proc: Other(i) # i

VARIABLES
  turn,          \* current turn owner in Proc
  want,          \* [Proc -> BOOLEAN], request flags
  pc,            \* [Proc -> {"N","T","C"}], control state: N=noncritical, T=trying, C=critical
  h_turn,        \* history sequence of turn assignments, Seq(Proc)
  s              \* [Proc -> {0,1,2,3}], stuttering substep for entry protocol

vars == << turn, want, pc, h_turn, s >>

PCStates == {"N","T","C"}

TypeOK ==
  /\ turn \in Proc
  /\ want \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCStates]
  /\ s \in [Proc -> {0,1,2,3}]
  /\ IsHistory(h_turn, Proc)
  /\ \A i \in Proc:
        IF pc[i] = "T" THEN s[i] \in 1..3 ELSE s[i] = 0

Init ==
  /\ TypeOK
  /\ want = [i \in Proc |-> FALSE]
  /\ pc   = [i \in Proc |-> "N"]
  /\ s    = [i \in Proc |-> 0]
  /\ h_turn = << >>
  /\ turn \in Proc

\* Actions for process i
Try(i) ==
  /\ i \in Proc
  /\ pc[i] = "N"
  /\ s[i] = 0
  /\ pc' = [pc EXCEPT ![i] = "T"]
  /\ s'  = [s  EXCEPT ![i] = 1]
  /\ UNCHANGED << turn, want, h_turn >>

St1(i) ==
  /\ i \in Proc
  /\ s[i] = 1
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ s'    = [s    EXCEPT ![i] = 2]
  /\ UNCHANGED << turn, pc, h_turn >>

St2(i) ==
  /\ i \in Proc
  /\ s[i] = 2
  /\ turn' = Other(i)
  /\ h_turn' = AppendHist(h_turn, turn')
  /\ s'    = [s EXCEPT ![i] = 3]
  /\ UNCHANGED << want, pc >>

Gate(i) ==
  ~want[Other(i)] \/ turn = i

Wait(i) ==
  /\ i \in Proc
  /\ s[i] = 3
  /\ ~Gate(i)
  /\ UNCHANGED vars

Enter(i) ==
  /\ i \in Proc
  /\ s[i] = 3
  /\ Gate(i)
  /\ pc' = [pc EXCEPT ![i] = "C"]
  /\ s'  = [s  EXCEPT ![i] = 0]
  /\ UNCHANGED << turn, want, h_turn >>

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "C"
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ pc'   = [pc   EXCEPT ![i] = "N"]
  /\ UNCHANGED << turn, h_turn, s >>

Next ==
  \E i \in Proc:
      Try(i)
    \/ St1(i)
    \/ St2(i)
    \/ Enter(i)
    \/ Exit(i)
    \/ Wait(i)

\* Safety: Mutual exclusion and typing
MutualExclusion ==
  \A i, j \in Proc: i # j => ~(pc[i] = "C" /\ pc[j] = "C")

Inv == TypeOK /\ MutualExclusion

\* Stepwise history consistency: if turn changes, append the new turn to history
HistConsistency ==
  [](turn' = turn \/ h_turn' = AppendHist(h_turn, turn'))

\* Liveness/Fairness: ensure progress through the three-step entry protocol when enabled
Fairness ==
  /\ \A i \in Proc: WF_vars(St1(i))
  /\ \A i \in Proc: WF_vars(St2(i))
  /\ \A i \in Proc: WF_vars(Enter(i))

Spec == Init /\ [][Next]_vars /\ HistConsistency /\ Fairness

\* Map this lock-with-stuttering to Peterson's micro-steps:
\* "N" -> "ncs", "T" with s=1 -> "try1", s=2 -> "try2", s=3 -> "try3", "C" -> "cs"
Ppc ==
  [ i \in Proc |->
      IF pc[i] = "N" THEN "ncs"
      ELSE IF pc[i] = "T" /\ s[i] = 1 THEN "try1"
      ELSE IF pc[i] = "T" /\ s[i] = 2 THEN "try2"
      ELSE IF pc[i] = "T" /\ s[i] = 3 THEN "try3"
      ELSE IF pc[i] = "C" THEN "cs"
      ELSE "ncs"
  ]

P == INSTANCE Peterson
        WITH Proc <- Proc,
             Other <- Other,
             flag <- want,
             turn <- turn,
             pc   <- Ppc

\* The related Peterson behavior under the above mapping:
PetersonRel == P!Spec

====