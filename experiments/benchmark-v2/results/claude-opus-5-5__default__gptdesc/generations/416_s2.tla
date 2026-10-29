------------------------------- MODULE PrimeTest -------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

D == {1, 2}

Init ==
    /\ x = [i \in D |-> 0]
    /\ y = 0

(* The argument d is the variable y. Priming d inside the EXCEPT update     *)
(* therefore means y'. The new value of x[1] is the next-state value of y.  *)
UsePrimed(d) == x' = [x EXCEPT ![1] = d']

(* The argument d is used unprimed. The new value of x[1] is the            *)
(* current-state value of y.                                                *)
UseUnprimed(d) == x' = [x EXCEPT ![1] = d]

PrimedBranch ==
    /\ y' = 1 - y
    /\ UsePrimed(y)
    /\ PrintT(<<"primed branch", y, y', x'>>)
    /\ Assert(x'[1] = y', "UsePrimed: x'[1] should equal y'")
    /\ Assert(x'[2] = x[2], "UsePrimed: x'[2] should be unchanged")

UnprimedBranch ==
    /\ y' = 1 - y
    /\ UseUnprimed(y)
    /\ PrintT(<<"unprimed branch", y, y', x'>>)
    /\ Assert(x'[1] = y, "UseUnprimed: x'[1] should equal y")
    /\ Assert(x'[2] = x[2], "UseUnprimed: x'[2] should be unchanged")

Stutter == UNCHANGED vars

Next ==
    \/ PrimedBranch
    \/ UnprimedBranch
    \/ Stutter

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in [D -> {0, 1}]
    /\ y \in {0, 1}

XDomainInv == DOMAIN x = D

Unchanged2Inv == x[2] = 0

THEOREM Spec => [](TypeOK /\ XDomainInv /\ Unchanged2Inv)
================================================================================