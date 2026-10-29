------------------------------ MODULE PrimedExprTest ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1

(* Operator whose argument is a primed expression at the call site *)
Inc(a) == a + 1

(* Action-level operator that refers to x' directly *)
XPrimePlus(n) == x' + n

(* Function defined in terms of the primed variable *)
FPrime == [i \in {1, 2} |-> x' + i]

Next ==
    /\ x' = 2
    /\ y' = y
    /\ Print(<<"x' =", x'>>, TRUE)
    \* Function definitions using x'
    /\ LET f[i \in {1, 2}] == x' * i
       IN  Assert(f[1] = 2 /\ f[2] = 4, "Failed: recursive-style function definition with x'")
    /\ Assert(FPrime[1] = 3 /\ FPrime[2] = 4, "Failed: function constructor with x'")
    \* Set expressions using x'
    /\ Assert({x'} = {2}, "Failed: set enumeration with x'")
    /\ Assert({i \in {1, 2, 3} : i = x'} = {2}, "Failed: set filter with x'")
    /\ Assert({i + x' : i \in {0, 1}} = {2, 3}, "Failed: set map with x'")
    /\ Assert(x' \in {1, 2}, "Failed: set membership with x'")
    \* CHOOSE using x'
    /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Failed: CHOOSE with x'")
    \* Function override (EXCEPT) using x'
    /\ LET g == [i \in {1, 2} |-> 0]
       IN  Assert([g EXCEPT ![1] = x'][1] = 2, "Failed: EXCEPT with x'")
    /\ Assert([FPrime EXCEPT ![2] = @ + x'][2] = 6, "Failed: EXCEPT with @ and x'")
    \* CASE using x'
    /\ Assert(CASE x' = 1 -> FALSE
                 [] x' = 2 -> TRUE
                 [] OTHER  -> FALSE,
              "Failed: CASE with x'")
    \* IF-THEN-ELSE using x'
    /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Failed: IF with x'")
    \* Quantifiers using x'
    /\ Assert(\A i \in {x'} : i = 2, "Failed: universal quantifier with x'")
    /\ Assert(\E i \in {1, 2, 3} : i = x', "Failed: existential quantifier with x'")
    \* Implication using x'
    /\ Assert((x' = 2) => (y' = 1), "Failed: implication with x'")
    /\ Assert((x' = 1) => FALSE, "Failed: vacuous implication with x'")
    \* Operator calls using x'
    /\ Assert(Inc(x') = 3, "Failed: operator call with x' argument")
    /\ Assert(XPrimePlus(1) = 3, "Failed: operator body referencing x'")
    \* Primed tuple / unchanged-style expressions
    /\ Assert(<<x, y>>' = <<2, 1>>, "Failed: primed tuple expression")
    /\ Assert((x + y)' = 3, "Failed: primed compound expression")

Spec == Init /\ [][Next]_vars

\* Safety invariants
TypeOK ==
    /\ x \in {1, 2}
    /\ y = 1

YConstant == y = 1

=============================================================================