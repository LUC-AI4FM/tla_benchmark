---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeans,      \* An upper bound on the number of beans for the model checker
          InitialBlack,  \* The initial number of black beans
          InitialWhite   \* The initial number of white beans

ASSUME InitialBlack \in 0..MaxBeans
ASSUME InitialWhite \in 0..MaxBeans
ASSUME InitialBlack + InitialWhite > 1
ASSUME (InitialBlack + InitialWhite) <= MaxBeans

VARIABLES can

vars == <<can>>

\* The state is a record holding the counts of black and white beans.
Init == can = [black |-> InitialBlack, white |-> InitialWhite]

\* ---- Actions ----

\* Rule: If two black beans are removed, one black bean is put back.
\* Net change: The number of black beans decreases by one.
RemoveTwoBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Rule: If two white beans are removed, one black bean is put back.
\* Net change: White beans decrease by 2, black beans increase by 1.
RemoveTwoWhite ==
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Rule: If one black and one white bean are removed, one white bean is put back.
\* Net change: The number of black beans decreases by one.
RemoveOneOfEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* If only one bean remains, the process terminates. This is a stuttering step.
Terminate ==
    /\ can.black + can.white = 1
    /\ UNCHANGED vars

\* The next-state relation is the disjunction of all possible actions.
Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneOfEach
    \/ Terminate

\* The main specification, including a weak fairness condition on the system
\* to ensure it does not stutter indefinitely before termination.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---- Properties ----

TotalBeans == can.black + can.white

\* Safety Invariant: The bean counts remain valid natural numbers.
TypeInvariant == can \in [black: 0..MaxBeans, white: 0..MaxBeans]

\* Safety Invariant: The parity of the number of white beans never changes.
WhiteParityInvariant == (can.white % 2) = (InitialWhite % 2)

\* Safety Invariant: The color of the final bean is determined by the
\* initial parity of the white beans.
FinalBeanColorIsCorrect ==
    (TotalBeans = 1) =>
        IF (InitialWhite % 2 = 0)
        THEN can.white = 0  \* The last bean is black
        ELSE can.white = 1  \* The last bean is white

\* This temporal property states that the total number of beans
\* strictly decreases by one at each step until only one bean remains.
TotalBeansMonotonicallyDecreases ==
    [][TotalBeans > 1 => TotalBeans' = TotalBeans - 1]_vars

\* Liveness Property: The process must eventually reach a terminal state.
EventualTermination == <> (TotalBeans = 1)

=============================================================================