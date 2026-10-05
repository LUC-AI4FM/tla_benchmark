---------------------------- MODULE FactorialCounter ----------------------------

EXTENDS Integers

CONSTANTS SmallN, LargeN

ASSUME SmallN \in Nat /\ LargeN \in Nat /\ SmallN <= LargeN

VARIABLES counter

(* Recursive factorial function - total and terminating for natural numbers *)
RECURSIVE Factorial(_)
Factorial(n) ==
    IF n <= 1 THEN 1
    ELSE n * Factorial(n - 1)

(* The two concrete factorial values computed from the constants *)
SmallFactorial == Factorial(SmallN)
LargeFactorial == Factorial(LargeN)

(* The set of allowed counter values *)
AllowedValues == {SmallFactorial, LargeFactorial}

(* Type invariant *)
TypeOK == counter \in Int

(* Initial state: counter must be zero *)
Init == counter = 0

(* Short update: atomically set counter to factorial of small constant *)
ShortUpdate == counter' = SmallFactorial

(* Long update: atomically set counter to factorial of larger constant *)
LongUpdate == counter' = LargeFactorial

(* Transition relation: nondeterministically choose either update *)
Next == ShortUpdate \/ LongUpdate

(* Overall specification with weak fairness on both transitions *)
Spec == Init /\ [][Next]_counter /\ WF_counter(ShortUpdate) /\ WF_counter(LongUpdate)

(* ========================