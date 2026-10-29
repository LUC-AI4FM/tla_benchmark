---- MODULE PrimingTest ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat

VARIABLES x, y

vars == <<x, y>>

\* Helper operators
Inc(a)    == a + 1
Double(a) == 2 * a
GetX      == x
GetY      == y
Sum       == x + y
Pair      == <<x, y>>

TypeOK == /\ x \in 0..N
          /\ y \in 0..N

Init == /\ x = 0
        /\ y = 0

Step ==
  /\ x < N
  /\ x' = x + 1
  /\ y' = Inc(y)
  \* Priming direct variable references
  /\ Assert(x' = x + 1, "x' should equal x + 1")
  /\ Assert(y' = y + 1, "y' should equal y + 1")
  \* Priming zero-argument operator applications (not variables)
  /\ Assert(GetX' = x', "GetX' should equal x'")
  /\ Assert(GetY' = y', "GetY' should equal y'")
  /\ Assert(Sum' = x' + y', "Sum' should equal x' + y'")
  /\ Assert(Pair' = <<x', y'>>, "Pair' should equal <<x', y'>>")
  \* Priming operator applications with arguments
  /\ Assert(Inc(x)' = Inc(x'), "Inc(x)' should equal Inc(x')")
  /\ Assert(Inc(x)' = x' + 1, "Inc(x)' should equal x' + 1")
  /\ Assert(Double(y)' = 2 * y', "Double(y)' should equal 2 * y'")
  /\ Assert(Inc(x) = x', "Unprimed Inc(x) should equal x'")
  \* Priming LET-bound names
  /\ LET z == x + y
         w == Double(x)
     IN  /\ Assert(z = x + y, "LET z should equal x + y")
         /\ Assert(z' = x' + y', "LET z' should equal x' + y'")
         /\ Assert(w' = 2 * x', "LET w' should equal 2 * x'")
         /\ Assert(w = 2 * x, "LET w should equal 2 * x")
  \* LET body containing primed variables
  /\ LET d == x' - x
     IN  Assert(d = 1, "x' - x should equal 1")
  \* Priming conditional expressions
  /\ Assert((IF x' > x THEN y' ELSE x) = y',
            "IF with primed condition should take THEN branch")
  /\ Assert((IF x > N THEN x ELSE y)' = y',
            "Primed IF should evaluate condition and branches in next state")
  /\ Assert((IF x = N - 1 THEN Inc(x) ELSE x + 1) = x',
            "Both branches should produce x'")
  /\ PrintT(<<"step", x, y, "->", x', y'>>)

Done == /\ x = N
        /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Trivial invariant
Inv == TRUE

\* Additional sanity invariants
XEqualsY == x = y

\* Liveness: the counter eventually reaches N
Termination == <>(x = N)

====