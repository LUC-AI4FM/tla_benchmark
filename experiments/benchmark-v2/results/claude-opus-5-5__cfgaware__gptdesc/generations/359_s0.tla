---------------------------- MODULE PrimedExprTest ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1

Op(a) == a + 1

TNext ==
    /\ x' = 2
    /\ y' = y
    \* Quantifiers
    /\ \A i \in {x'} : i = 2
    /\ \E i \in {x', 3} : i = 2
    \* CHOOSE
    /\ (CHOOSE i \in {x', 3} : i < 3) = 2
    \* Set expressions
    /\ {i \in {x', 3} : i = x'} = {2}
    /\ {x' + i : i \in {0}} = {2}
    /\ {x'} \cup {3} = {2, 3}
    \* Function definitions
    /\ LET f[i \in {1}] == x' + i IN f[1] = 3
    /\ [i \in {1} |-> x'][1] = 2
    \* EXCEPT updates
    /\ [[i \in {1} |-> 0] EXCEPT ![1] = x'][1] = 2
    /\ [[i \in {1} |-> x'] EXCEPT ![1] = @ + 1][1] = 3
    \* Function-set constructors
    /\ [{1} -> {x'}] = {[i \in {1} |-> 2]}
    /\ [a : {x'}] = {[a |-> 2]}
    \* Implication
    /\ (x' = 2) => (y' = 1 \/ y' # 1)
    /\ ~(x' = 2) => FALSE
    \* CASE
    /\ (CASE x' = 2 -> TRUE
          [] OTHER  -> FALSE)
    \* DOMAIN
    /\ DOMAIN [i \in {x'} |-> i] = {2}
    \* Operator application
    /\ Op(x') = 3
    \* TLC operators
    /\ Print(<<"x'", x'>>, TRUE)
    /\ Assert(x' = 2, "Primed expression evaluated incorrectly")

Next ==
    \/ TNext
    \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

Inv ==
    /\ x \in {1, 2}
    /\ y = 1

=============================================================================