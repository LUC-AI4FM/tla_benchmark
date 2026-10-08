---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT MaxBeans

VARIABLES beans

beans == [black |-> 0, white |-> 0]

Init ==
  /\ beans \in [1..MaxBeans]
  /\ black \in Nat
  /\ white \in Nat
  /\ black + white = beans

DrawBlack ==
  /\ black > 0
  /\ white >= 0
  /\ beans' = [black |-> black - 1, white |-> white]

DrawWhite ==
  /\ white > 0
  /\ black >= 0
  /\ beans' = [black |-> black, white |-> white - 1]

DrawTwo ==
  /\ DrawBlack
  /\ DrawWhite

Step ==
  \/ (black > 1 /\ beans' = [black |-> black - 2, white |-> white + 1])
  \/ (white > 1 /\ beans' = [black |-> black + 1, white |-> white - 2])
  \/ (black > 0 /\ white > 0 /\ beans' = [black |-> black - 1, white |-> white])

Next ==
  Step

Spec == Init /\ [][Next]_beans

THEOREM Spec => []<>((black + white) = 1)

THEOREM Spec => [](white % 2 = (InitWhite % 2))

THEOREM Spec => <>(black = 1 /\ white = 0) \/ <>(black = 0 /\ white = 1)

THEOREM Spec => []<>(black > 0 /\ white > 0) => <>((black + white) = 1)

Fairness == WF_vars(Next, beans)

MaxBeans == 100

InitWhite == (beans[white])

=============================================================================