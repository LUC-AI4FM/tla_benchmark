---------------------------- MODULE ParityChecker ----------------------------
EXTENDS Integers

CONSTANT N

VARIABLE result, pc, stack

Init == (pc = "start") ∧ (stack = <<N>>) ∧ (result = FALSE)

start == (* start the parity check procedure *)
          (pc' = "check") ∧ (stack' = <<N>>) ∧ (result' = result)

check == (* recursive parity checking procedure *)
         IF Head(stack) = 0 THEN
           (* base case: argument is zero, set result to TRUE *)
           (pc' = "return") ∧ (stack' = Tail(stack)) ∧ (result' = TRUE)
         ELSE IF Head(stack) = 1 THEN
           (* base case: argument is one, set result to FALSE *)
           (pc' = "return") ∧ (stack' = Tail(stack)) ∧ (result' = FALSE)
         ELSE
           (* recursive call with decremented argument *)
           (pc' = "check") ∧ (stack' = <<Head(stack) - 1>> ⊕ Tail(stack)) ∧ (result' = result)

return == (* return from procedure call *)
          IF stack = <<>> THEN
            (* no more pending calls, set final result *)
            (pc' = "done") ∧ (stack' = stack) ∧ (result' = result)
          ELSE
            (* pop return target and resume previous call *)
            (pc' = "check") ∧ (stack' = Tail(stack)) ∧ (result' = result)

done == (* final state: result is stable *)
       (pc' = pc) ∧ (stack' = stack) ∧ (result' = result)

Spec == Init ∧ [][start ∨ check ∨ return ∨ done]_<<pc, stack, result>>

Termination == <>[]<>(pc = "done")

THEOREM Spec => []Termination
=============================================================================