---------------------------- MODULE IterativePower ----------------------------
EXTENDS Integers

CONSTANTS BaseDomain,   \* finite set of integers allowed as the base
          ExpDomain     \* finite set of natural numbers allowed as the exponent

ASSUME BaseDomain \subseteq Int /\ BaseDomain # {}
ASSUME ExpDomain \subseteq Nat /\ ExpDomain # {}

VARIABLES base,    \* input base (never changes)
          exp,     \* input exponent (never changes)
          prod,    \* running product
          count,   \* number of multiplications performed so far
          pc,      \* control state: "running" or "done"
          result   \* output, meaningful only once pc = "done"

vars == <<base, exp, prod, count, pc, result>>

\* Mathematical reference definition of exponentiation (independent of implementation)
RECURSIVE Pow(_, _)
Pow(b, n) == IF n = 0 THEN 1 ELSE b * Pow(b, n - 1)

NoResult == "none"

-----------------------------------------------------------------------------
Init ==
    /\ base \in BaseDomain
    /\ exp \in ExpDomain
    /\ prod = 1
    /\ count = 0
    /\ pc = "running"
    /\ result = NoResult

\* Perform one multiplication step
Multiply ==
    /\ pc = "running"
    /\ count < exp
    /\ prod' = prod * base
    /\ count' = count + 1
    /\ UNCHANGED <<base, exp, pc, result>>

\* Halt once the number of multiplications equals the exponent
Finish ==
    /\ pc = "running"
    /\ count = exp
    /\ pc' = "done"
    /\ result' = prod
    /\ UNCHANGED <<base, exp, prod, count>>

\* Once halted, the system stutters
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Multiply \/ Finish \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Multiply) /\ WF_vars(Finish)

-----------------------------------------------------------------------------
\* Type correctness
TypeOK ==
    /\ base \in Int
    /\ exp \in Nat
    /\ prod \in Int
    /\ count \in Nat
    /\ pc \in {"running", "done"}
    /\ result \in Int \cup {NoResult}

\* Safety of inputs: inputs always within the allowed domains
InputsValid ==
    /\ base \in BaseDomain
    /\ exp \in ExpDomain

\* Loop invariant: product equals base^count
ProductInv == prod = Pow(base, count)

\* Count never exceeds the exponent
CountBound == 0 <= count /\ count <= exp

\* When halted, all multiplications have been performed
DoneImpliesComplete == (pc = "done") => (count = exp)

\* Partial correctness: a terminated computation yields base^exp
PartialCorrectness == (pc = "done") => (result = Pow(base, exp))

\* Result is only produced on halting
ResultOnlyWhenDone == (pc = "running") => (result = NoResult)

Inv ==
    /\ TypeOK
    /\ InputsValid
    /\ ProductInv
    /\ CountBound
    /\ DoneImpliesComplete
    /\ PartialCorrectness
    /\ ResultOnlyWhenDone

-----------------------------------------------------------------------------
\* No unintended state corruption: inputs never change
InputsUnchanged == [][base' = base /\ exp' = exp]_vars

\* Count increases monotonically (by at most one per step)
CountMonotonic == [][count' = count \/ count' = count + 1]_vars

\* Once halted, stays halted with the same result
HaltStable == [][pc = "done" => (pc' = "done" /\ result' = result)]_vars

-----------------------------------------------------------------------------
\* Progress / termination
Termination == <>(pc = "done")

\* Eventually halts with the correct result
EventuallyCorrect == <>(pc = "done" /\ result = Pow(base, exp))

\* Count eventually reaches the exponent
CountReachesExp == <>(count = exp)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => InputsUnchanged /\ CountMonotonic /\ HaltStable
THEOREM Spec => Termination /\ EventuallyCorrect /\ CountReachesExp

=============================================================================