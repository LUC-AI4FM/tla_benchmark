---- MODULE LockWithHistory ----
EXTENDS Naturals, Sequences

CONSTANT Proc
ASSUME Proc = {0,1}

VARIABLES pc, s, turn, h_turn

vars == <<pc, s, turn, h_turn>>

Other(i) == CHOOSE j \in Proc: j # i

Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ s = [i \in Proc |-> 0]
  /\ turn \in Proc
  /\ h_turn = << >>

PFlag ==
  [ i \in Proc |->
      IF pc[i] = "idle" THEN FALSE
      ELSE IF pc[i] = "trying" THEN s[i] >= 1
      ELSE TRUE
  ]

PPc ==
  [ i \in Proc |->
      IF pc[i] = "idle" THEN "idle"
      ELSE IF pc[i] = "cs" THEN "cs"
      ELSE IF s[i] = 1 THEN "setFlag"
      ELSE IF s[i] = 2 THEN "setTurn"
      ELSE "wait"
  ]

TryStart(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ s' = [s EXCEPT ![i] = 1]
  /\ UNCHANGED <<turn, h_turn>>

SetFlagStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "trying"
  /\ s[i] = 1
  /\ s' = [s EXCEPT ![i] = 2]
  /\ UNCHANGED <<pc, turn, h_turn>>

SetTurnStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "trying"
  /\ s[i] = 2
  /\ turn' = Other(i)
  /\ s' = [s EXCEPT ![i] = 3]
  /\ h_turn' = Append(h_turn, [by |-> i, to |-> Other(i)])
  /\ UNCHANGED pc

WaitOrEnter(i) ==
  /\ i \in Proc
  /\ pc[i] = "trying"
  /\ s[i] = 3
  /\ (~PFlag[Other(i)] \/ turn = i)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ s' = [s EXCEPT ![i] = 0]
  /\ UNCHANGED <<turn, h_turn>>

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ s' = [s EXCEPT ![i] = 0]
  /\ UNCHANGED <<turn, h_turn>>

ProcStep(i) == TryStart(i) \/ SetFlagStep(i) \/ SetTurnStep(i) \/ WaitOrEnter(i) \/ ExitCS(i)

Next == \E i \in Proc: ProcStep(i)

TypeInv ==
  /\ pc \in [Proc -> {"idle", "trying", "cs"}]
  /\ s \in [Proc -> 0..3]
  /\ turn \in Proc
  /\ h_turn \in Seq([by: Proc, to: Proc])
  /\ \A i \in Proc:
        IF pc[i] = "idle" THEN s[i] = 0
        ELSE IF pc[i] = "cs" THEN s[i] = 0
        ELSE s[i] \in 1..3

Mutex ==
  \A i, j \in Proc: i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

HistInv ==
  \A k \in 1..Len(h_turn):
    /\ h_turn[k].by \in Proc
    /\ h_turn[k].to = Other(h_turn[k].by)

Inv == TypeInv /\ Mutex /\ HistInv

Fairness == \A i \in Proc: WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

PetersonI == INSTANCE Peterson
  WITH Proc <- Proc,
       flag <- PFlag,
       turn <- turn,
       pc   <- PPc
====