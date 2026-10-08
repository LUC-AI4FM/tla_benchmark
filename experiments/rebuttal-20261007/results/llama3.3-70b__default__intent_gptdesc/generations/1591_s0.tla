```
MODULE ParityChecker
EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES pc, args, results, returnTargets

Init ==
  /\ pc = "start"
  /\ args = <<N>>
  /\ results = <<
  /\ returnTargets = <<>>

Next ==
  /\ (pc = "start") => 
    /\ pc' = "checkParity"
    /\ args' = <<N>>
    /\ results' = <<
    /\ returnTargets' = <<"start">>
  /\ (pc = "checkParity") =>
    /\ IF (Head(args) = 0)
      THEN
        /\ pc' = "return"
        /\ args' = Tail(args)
        /\ results' = Append(results, TRUE)
        /\ returnTargets' = returnTargets
      ELSE
        /\ IF (Head(args) mod 2 = 0)
          THEN
            /\ pc' = "checkParity"
            /\ args' = Append(Tail(args), Head(args) - 1)
            /\ results' = results
            /\ returnTargets' = Append(returnTargets, "checkParity")
          ELSE
            /\ pc' = "checkParity"
            /\ args' = Append(Tail(args), Head(args) - 1)
            /\ results' = results
            /\ returnTargets' = Append(returnTargets, "checkParity")
    /\ (pc = "return") =>
      /\ IF (returnTargets = <<>>)
        THEN
          /\ pc' = "done"
          /\ args' = <<
          /\ results' = results
          /\ returnTargets' = <<
        ELSE
          /\ pc' = Head(returnTargets)
          /\ args' = Tail(args)
          /\ results' = results
          /\ returnTargets' = Tail(returnTargets)

Spec == Init /\ [][Next]_<<pc, args, results, returnTargets>>

THEOREM Spec => []<>(pc = "done" /\ results = <<(N mod 2 = 0)>>)
THEOREM Spec => <>[](pc = "done")
THEOREM Spec => [](Len(args) <= N + 1)
THEOREM Spec => [](Len(returnTargets) <= N)

INVARIANT pc \in {"start", "checkParity", "return", "done"}
INVARIANT args /= <<
INVARIANT results /= <<
INVARIANT returnTargets /= <<

FAIRNESS Next
```