---- MODULE PrimeEvaluation ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

MaxX == 6

TypeOK == x \in Nat /\ y \in Nat

Init == /\ x = 1
        /\ y = 3

Inc1 == /\ x < MaxX
        /\ x' = x + 1
        /\ y' = y
        /\ Assert(x' = x + 1, "Inc1: counter' # counter + 1")
        /\ Assert(y' = y, "Inc1: auxiliary changed")

Inc2 == /\ x < MaxX
        /\ y' = y
        /\ x' = x + 1
        /\ Assert((x + 1)' = x + 2, "Inc2: (x+1)' # x + 2")
        /\ Assert((x + y)' = x' + y', "Inc2: primed subexpression mismatch")
        /\ Assert((x' - x) = 1, "Inc2: difference of new and old counter # 1")

Inc3 == /\ x < MaxX
        /\ x' = x + 1
        /\ y' = y
        /\ LET z == x + y
               p == x = 1
           IN /\ Assert(z' = z + 1, "Inc3: LET definition z' # z + 1")
              /\ Assert(z = x + y, "Inc3: LET definition not evaluated in pre-state")
              /\ Assert(z' = x' + y', "Inc3: LET definition not evaluated in post-state")
              /\ Assert(p' = (x' = 1), "Inc3: primed LET predicate mismatch")
              /\ Assert(p = (x = 1), "Inc3: unprimed LET predicate mismatch")
              /\ Assert(~(p /\ p'), "Inc3: predicate true in both pre- and post-state")

Inc4 == /\ x < MaxX
        /\ x' = x + 1
        /\ y' = y
        /\ Assert(x' > x, "Inc4: new counter not greater than old")
        /\ Assert((x > 0)' = (x' > 0), "Inc4: primed predicate mismatch")
        /\ Assert((x = x')' = TRUE \/ (x = x')' = FALSE, "Inc4: boolean prime malformed")
        /\ Assert(~(x = x'), "Inc4: pre/post confusion, x = x'")
        /\ Assert((y = 3)' /\ (y = 3), "Inc4: auxiliary not 3 in pre or post state")

Increment == Inc1 \/ Inc2 \/ Inc3 \/ Inc4

Stutter == /\ UNCHANGED vars
           /\ Assert(x' = x /\ y' = y, "Stutter: state changed")

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_vars

Inv == /\ TypeOK
       /\ y = 3
       /\ x \in 1..MaxX

AuxPreserved == [][y' = y]_vars

IncrementCorrect == [][x' = x + 1 \/ x' = x]_vars

====