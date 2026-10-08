```tla
MODULE CoffeeCan
EXTENDS Integers

CONSTANTS MaxBeans
VARIABLES blackBeans, whiteBeans, totalBeans

Init ==
  /\ totalBeans \in 1..MaxBeans
  /\ blackBeans \in 0..totalBeans
  /\ whiteBeans = totalBeans - blackBeans

Next ==
  /\ totalBeans > 1
  /\ (blackBeans >= 2 /\ 
      /\ totalBeans' = totalBeans - 1
      /\ blackBeans' = blackBeans - 1
      /\ whiteBeans' = whiteBeans)
    \/
     (whiteBeans >= 2 /\ 
      /\ totalBeans' = totalBeans - 1
      /\ blackBeans' = blackBeans + 1
      /\ whiteBeans' = whiteBeans - 2)
    \/
     (blackBeans > 0 /\ whiteBeans > 0 /\ 
      /\ totalBeans' = totalBeans - 1
      /\ blackBeans' = blackBeans - 1
      /\ whiteBeans' = whiteBeans + 1)

Spec ==
  Init /\ [][Next]_<<blackBeans, whiteBeans, totalBeans>>
  /\ WF_<<blackBeans, whiteBeans, totalBeans>>(Next)

THEOREM Spec => []<>totalBeans = 1

THEOREM Spec => [](totalBeans' < totalBeans)

THEOREM Spec => [](whiteBeans % 2 = (whiteBeans') % 2)

THEOREM Spec => 
  IF Init /\ (whiteBeans % 2 = 0) THEN []<>(totalBeans = 1 /\ blackBeans = 1)
  ELSE IF Init /\ (whiteBeans % 2 = 1) THEN []<>(totalBeans = 1 /\ whiteBeans = 1)

THEOREM Spec => 
  IF Init /\ (whiteBeans % 2 = 0) THEN []<>(blackBeans > 0 /\ whiteBeans = 0)
  ELSE IF Init /\ (whiteBeans % 2 = 1) THEN []<>(blackBeans = 0 /\ whiteBeans > 0)

```

To model-check this specification for a concrete maximum bean count, such as 100, you would instantiate the `MaxBeans` constant with that value.