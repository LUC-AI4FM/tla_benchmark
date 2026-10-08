------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES proc, arg, result, oddCount, evenToOddCount

(* Initial state *)
Init == 
  proc = "Even" /\ arg = N /\ result = FALSE /\ oddCount = 0 /\ evenToOddCount = 0

(* Transition relation *)
Next ==
  (proc = "Even" /\ arg = 0) => (proc' = "Done" /\ result' = TRUE /\ arg' = arg /\ oddCount' = oddCount /\ evenToOddCount' = evenToOddCount) \/
  (proc = "Even" /\ arg > 0) => (proc' = "Odd" /\ arg' = arg - 1 /\ oddCount' = oddCount + 1 /\ evenToOddCount' = evenToOddCount + 1) \/
  (proc = "Odd" /\ arg = 0) => (proc' = "Done" /\ result' = FALSE /\ arg' = arg /\ oddCount' = oddCount /\ evenToOddCount' = evenToOddCount) \/
  (proc = "Odd" /\ arg > 0) => (proc' = "Even" /\ arg' = arg - 1 /\ oddCount' = oddCount /\ evenToOddCount' = evenToOddCount)

Spec == Init /\ [][Next]_<<proc, arg, result, oddCount, evenToOddCount>>

Termination == []<>(proc = "Done")

THEOREM RecursionCounts ==
  []((proc="Done") => (oddCount = 3 /\ evenToOddCount = 3))

====