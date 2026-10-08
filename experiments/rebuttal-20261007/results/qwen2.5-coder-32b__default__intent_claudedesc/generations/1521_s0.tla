------------------------------- MODULE CoffeeCan -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxBeans \* Maximum number of beans in the can

VARIABLES WhiteCount, TotalBeans

Init == /\ WhiteCount \in 0..MaxBeans
        /\ TotalBeans = WhiteCount + (MaxBeans - WhiteCount)

Next ==
    \/ /\ TotalBeans > 1
       /\ \/ /\ WhiteCount >= 2
              /\ WhiteCount' = WhiteCount - 2
              /\ TotalBeans' = TotalBeans - 1
          \/ /\ WhiteCount < TotalBeans - 1
             /\ WhiteCount' = WhiteCount + 1
             /\ TotalBeans' = TotalBeans - 1
          \/ /\ WhiteCount > 0
             /\ WhiteCount' = WhiteCount - 1
             /\ TotalBeans' = TotalBeans - 1

Spec ==
    /\ Init
    /\ [][Next]_<<WhiteCount, TotalBeans>>
    /\ WF_next(<<WhiteCount, TotalBeans>>)

\* Properties
DecreasingTotal == \A s, s' \in State: s' \in Next(s) => s'.TotalBeans < s.TotalBeans

ParityInvariant ==
    \A s \in State: Even(s.WhiteCount) = Even(s'.WhiteCount)
        \/ s.TotalBeans = 1

Termination ==
    <>[](TotalBeans = 1)

FinalColor ==
    [](TotalBeans = 1 => (Even(WhiteCount) => WhiteCount' = 0) /\ (\neg Even(WhiteCount) => WhiteCount' = 1))

State == [WhiteCount \in 0..MaxBeans, TotalBeans \in 0..MaxBeans]

WF_next(vars) ==
    \/ vars \notin State
    \/ \E s \in State: vars = <<s.WhiteCount, s.TotalBeans>> /\ \E s' \in State: s' \in Next(s)

=============================================================================