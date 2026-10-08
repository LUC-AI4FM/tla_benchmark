MODULE DigitStateMachine
EXTENDS Naturals

VARIABLE state

Init ==
  state = 0

Next ==
  \E newState \in {0,2,4,6,8} :
    (state' = newState)

Even(n) == (n % 2 = 0)

Safety ==
  state \in 0..9 /\ Even(state)

Spec ==
  Init /\ [][Next]_state

===============================================================================