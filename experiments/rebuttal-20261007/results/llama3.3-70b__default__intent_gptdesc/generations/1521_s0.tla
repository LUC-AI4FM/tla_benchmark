```
MODULE CoffeeCan
EXTENDS Integers

CONSTANTS MaxBeans
VARIABLES blackBeans, whiteBeans

Init ==
  /\ blackBeans \in Nat
  /\ whiteBeans \in Nat
  /\ blackBeans + whiteBeans > 0

Next ==
  /\ (blackBeans >= 2 /\ whiteBeans = 0)
      => (blackBeans' = blackBeans - 1)
  /\ (whiteBeans >= 2 /\ blackBeans = 0)
      => (whiteBeans' = whiteBeans - 1)
  /\ (blackBeans > 0 /\ whiteBeans > 0)
      => ((blackBeans' = blackBeans - 1 /\ whiteBeans' = whiteBeans) 
          \/ (blackBeans' = blackBeans + 1 /\ whiteBeans' = whiteBeans - 2))
  /\ (blackBeans < 2 /\ whiteBeans < 2)
      => (UNCHANGED <<blackBeans, whiteBeans>>)

Spec == Init /\ [][Next]_<<blackBeans, whiteBeans>>
Termination == <>(blackBeans + whiteBeans = 1)

THEOREM Spec => []((blackBeans + whiteBeans) > 0)
THEOREM Spec => [](blackBeans >= 0 /\ whiteBeans >= 0)
THEOREM Spec => []((blackBeans + whiteBeans)' = (blackBeans + whiteBeans) - 1)
THEOREM Spec => <>(Termination)

Fairness == SF_VARIABLES(<<blackBeans, whiteBeans>>)
THEOREM Spec /\ Fairness => Termination

Invariant ==
  [](whiteBeans mod 2 = (whiteBeans') mod 2)

THEOREM Spec => Invariant
THEOREM Spec => []((whiteBeans mod 2 = 0) => (blackBeans' = 1 /\ whiteBeans' = 0))
THEOREM Spec => []((whiteBeans mod 2 = 1) => (blackBeans' = 0 /\ whiteBeans' = 1))

```
Note: The `SF_VARIABLES` operator is used to specify the fairness condition, which ensures that if a transition is enabled infinitely often, it will eventually occur. This assumption rules out pathological infinite deferral of enabled transitions.