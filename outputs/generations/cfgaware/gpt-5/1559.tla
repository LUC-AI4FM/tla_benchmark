------------------------------ MODULE LockWithHist ------------------------------

EXTENDS Sequences

(*
  Lock protocol with auxiliary history (h_turn) and stuttering (s) variables.
  - pc[i] in {"N","T","C"} for process i ∈ Proc: Noncritical, Trying, Critical.
  - s[i] in {0,1,2} encodes the three micro-steps of Peterson's entry:
      0: set flag[i] := TRUE
      1: set turn := Other(i)  (and record in h_turn)
      2: await (~flag[j] \/ turn = i), then enter CS
  - h_turn is a history sequence recording all assignments to turn.
*)

Proc == {0, 1}
Other(i) == IF i = 0 THEN 1 ELSE 0
Steps == {0, 1, 2}

VARIABLES pc, flag, turn, h_turn, s

varsHS == << pc, flag, turn, h_turn, s >>
varsP  == << pc, flag, turn, s >>

Last(seq) == seq[Len(seq)]

TypeOKHS ==
  /\ pc \in [Proc -> {"N","T","C"}]
  /\ flag \in [Proc -> BOOLEAN]
  /\ turn \in Proc
  /\ h_turn \in Seq(Proc)
  /\ s \in [Proc -> Steps]

Init ==
  /\ pc = [i \in Proc |-> "N"]
  /\ flag = [i \in Proc |-> FALSE]
  /\ turn \in Proc
  /\ h_turn = << >>
  /\ s = [i \in Proc |-> 0]

Try(i) ==
  /\ i \in Proc
  /\ pc[i] = "N"
  /\ pc' = [pc EXCEPT ![i] = "T"]
  /\ flag' = flag
  /\ turn' = turn
  /\ h_turn' = h_turn
  /\ s' = [s EXCEPT ![i] = 0]

Micro1(i) ==
  /\ i \in Proc
  /\ pc[i] = "T"
  /\ s[i] = 0
  /\ pc' = pc
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ turn' = turn
  /\ h_turn' = h_turn
  /\ s' = [s EXCEPT ![i] = 1]

Micro2(i) ==
  /\ i \in Proc
  /\ pc[i] = "T"
  /\ s[i] = 1
  /\ pc' = pc
  /\ flag' = flag
  /\ turn' = Other(i)
  /\ h_turn' = Append(h_turn, Other(i))
  /\ s' = [s EXCEPT ![i] = 2]

Micro3(i) ==
  /\ i \in Proc
  /\ pc[i] = "T"
  /\ s[i] = 2
  /\ (~ flag[Other(i)] \/ turn = i)
  /\ pc' = [pc EXCEPT ![i] = "C"]
  /\ flag' = flag
  /\ turn' = turn
  /\ h_turn' = h_turn
  /\ s' = [s EXCEPT ![i] = 0]

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "C"
  /\ pc' = [pc EXCEPT ![i] = "N"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ turn' = turn
  /\ h_turn' = h_turn
  /\ s' = s

Step(i) == Try(i) \/ Micro1(i) \/ Micro2(i) \/ Micro3(i) \/ Exit(i)

NextHS == \E i \in Proc : Step(i)

SpecHS == Init /\ [][NextHS]_varsHS

LockInv ==
  /\ \A i, j \in Proc : i # j => ~(pc[i] = "C" /\ pc[j] = "C")

TurnMatchesHistory ==
  /\ (Len(h_turn) = 0) \/ (Last(h_turn) = turn)

InvHS == TypeOKHS /\ LockInv /\ TurnMatchesHistory

Spec == SpecHS

(*
  A Peterson-style specification (PSpec) over the operational variables
  pc, flag, turn, s, ignoring the history variable h_turn. This mirrors
  the three-step entry protocol using s as the micro-step counter.
*)

PInit ==
  /\ pc = [i \in Proc |-> "N"]
  /\ flag = [i \in Proc |-> FALSE]
  /\ turn \in Proc
  /\ s = [i \in Proc |-> 0]

PTry(i) ==
  /\ i \in Proc
  /\ pc[i] = "N"
  /\ pc' = [pc EXCEPT ![i] = "T"]
  /\ flag' = flag
  /\ turn' = turn
  /\ s' = [s EXCEPT ![i] = 0]

PE1(i) ==
  /\ i \in Proc
  /\ pc[i] = "T"
  /\ s[i] = 0
  /\ pc' = pc
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ turn' = turn
  /\ s' = [s EXCEPT ![i] = 1]

PE2(i) ==
  /\ i \in Proc
  /\ pc[i] = "T"
  /\ s[i] = 1
  /\ pc' = pc
  /\ flag' = flag
  /\ turn' = Other(i)
  /\ s' = [s EXCEPT ![i] = 2]

PE3(i) ==
  /\ i \in Proc
  /\ pc[i] = "T"
  /\ s[i] = 2
  /\ (~ flag[Other(i)] \/ turn = i)
  /\ pc' = [pc EXCEPT ![i] = "C"]
  /\ flag' = flag
  /\ turn' = turn
  /\ s' = [s EXCEPT ![i] = 0]

PExit(i) ==
  /\ i \in Proc
  /\ pc[i] = "C"
  /\ pc' = [pc EXCEPT ![i] = "N"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ turn' = turn
  /\ s' = s

PNext == \E i \in Proc : PTry(i) \/ PE1(i) \/ PE2(i) \/ PE3(i) \/ PExit(i)

PSpec == PInit /\ [][PNext]_varsP

=============================================================================