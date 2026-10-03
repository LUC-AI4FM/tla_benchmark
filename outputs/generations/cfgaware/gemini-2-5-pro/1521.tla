---- MODULE CoffeeCan ----
EXTENDS Integers, TLC

CONSTANT MaxBeans

VARIABLE beans

\* The state is a record with the number of black and white beans.
TypeInvariant ==
    /\ beans.black \in Nat
    /\ beans.white \in Nat

\* The process starts with more than one bean, up to a maximum total.
Init ==
    /\ beans \in {[black: b, white: w] : b \in 0..MaxBeans, w \in 0..MaxBeans}
    /\ beans.black + beans.white > 1
    /\ beans.black + beans.white <= MaxBeans

\* Remove two black beans and put one black bean back.
RemoveBB ==
    /\ beans.black >= 2
    /\ beans' = [beans EXCEPT !.black = @ - 1]

\* Remove two white beans and put one black bean back.
RemoveWW ==
    /\ beans.white >= 2
    /\ beans' = [beans EXCEPT !.white = @ - 2, !.black = @ + 1]

\* Remove one black and one white bean and put one white bean back.
RemoveBW ==
    /\ beans.black >= 1
    /\ beans.white >= 1
    /\ beans' = [beans EXCEPT !.black = @ - 1]

\* The process is done when exactly one bean remains.
IsTerminal == beans.black + beans.white = 1

\* A stuttering step when the process is done.
Done ==
    /\ IsTerminal
    /\ UNCHANGED beans

\* The next-state relation.
Next ==
    \/ RemoveBB
    \/ RemoveWW
    \/ RemoveBW
    \/ Done

\* Helper operator for the total number of beans.
Total(b) == b.black + b.white

\* Property: The total number of beans never increases. This is a property
\* of the Next relation.
TotalBeansDecrease ==
    [Next]_beans => (Total(beans') <= Total(beans))

\* Property: The process must eventually terminate under weak fairness.
Termination ==
    WF_beans(Next) => <>IsTerminal

\* Property: The parity of the number of white beans is a loop invariant.
\* This is expressed as an implication over the initial state. For any given
\* initial state, the parity it starts with is preserved throughout.
WhiteBeanParity ==
    /\ (beans.white % 2 = 0) => [](beans.white % 2 = 0)
    /\ (beans.white % 2 = 1) => [](beans.white % 2 = 1)

\* Property: The color of the final bean is determined by the parity of the
\* initial number of white beans.
FinalBeanColorHypothesis ==
    /\ (beans.white % 2 = 0) => [](IsTerminal => beans.black = 1)
    /\ (beans.white % 2 = 1) => [](IsTerminal => beans.white = 1)

=============================================================================