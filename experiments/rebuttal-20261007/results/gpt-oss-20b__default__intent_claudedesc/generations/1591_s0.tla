MODULE EvenOdd
EXTENDS Naturals

N == 6

VARIABLES proc, n, done, oddCount, transitionCount

ProcType == {"Even", "Odd"}

Init ==
    /\ n = N
    /\ proc = "Even"
    /\ done = FALSE
    /\ oddCount = 0
    /\ transitionCount = 0

Next ==
    \/ (* Even case *)
       /\ ~done
       /\ proc = "Even"
       /\ IF n = 0 THEN
              /\ done' = TRUE
              /\ proc' = proc
              /\ n' = n
              /\ oddCount' = oddCount
              /\ transitionCount' = transitionCount
          ELSE
              /\ proc' = "Odd"
              /\ n' = n - 1
              /\ oddCount' = oddCount + 1
              /\ transitionCount' = transitionCount + 1
              /\ done' = FALSE
    \/ (* Odd case *)
       /\ ~done
       /\ proc = "Odd"
       /\ IF n = 0 THEN
              /\ done' = TRUE
              /\ proc' = proc
              /\ n' = n
              /\ oddCount' = oddCount
              /\ transitionCount' = transitionCount
          ELSE
              /\ proc' = "Even"
              /\ n' = n - 1
              /\ oddCount' = oddCount
              /\ transitionCount' = transitionCount
              /\ done' = FALSE

Spec == Init /\ [][Next]_<<proc, n, done, oddCount, transitionCount>>

Safety ==
    /\ [] (oddCount <= 3)
    /\ [] (transitionCount <= 3)

Liveness ==
    <> done

InvariantOddTransitionEquality ==
    [] (done => oddCount = 3 /\ transitionCount = 3)