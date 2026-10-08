MODULE LockProtocol

EXTENDS Naturals, Sequences, TLC

CONSTANTS P \* {0, 1}

VARIABLES flag, turn, h_turn, s

vars == <<flag, turn, h_turn, s>>

Init ==
  /\ flag = [p \in P |-> FALSE]
  /\ turn \in P
  /\ h_turn = << >>
  /\ s = 0

q(p) == CHOOSE q \in P : q # p

SetFlag(p) ==
  /\ flag'   = [flag EXCEPT ![p] = TRUE]
  /\ turn'   = q(p)
  /\ h_turn' = Append(h_turn, turn')
  /\ s'      = 1

WaitStep(p) ==
  /\ flag[q(p)]
  /\ (turn = q(p))
  /\ s'            = Mod(s + 1, 3)
  /\ UNCHANGED <<flag, turn, h_turn>>

EnterCS(p) ==
  /\ ~flag[q(p)]
  /\ s'      = 0
  /\ UNCHANGED <<flag, turn, h_turn>>

Exit(p) ==
  /\ flag'   = [flag EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<turn, h_turn, s>>

Next == \E p \in P:
          \/ SetFlag(p)
        \/ WaitStep(p)
        \/ EnterCS(p)
        \/ Exit(p)

SafetyInvariant ==
  ~ (flag[0] /\ flag[1])

Spec == Init /\ [][Next]_vars /\ SafetyInvariant

===============================================================================