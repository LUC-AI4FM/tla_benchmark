------------------------------- MODULE EuclidGCD -------------------------------

CONSTANTS N \* The upper bound for the second input value

VARIABLES x, y, originalY

(*--algorithm EuclidGCD
variables x = 24, y \in {1..N}, originalY = y;
begin
    while (x # 0) /\ (y # 0)
    do
        if x > y then
            x := x - y;
        else
            y := y - x;
        end if;
    od;
    print <<originalY, IF x = 0 THEN y ELSE x >>; \* Print the GCD and original second input for verification
end algorithm*)

\* Define the mathematical GCD operator using Euclid's algorithm
GCD(a, b) == CHOOSE g \in {1..a} : (g \divides a) /\ (g \divides b) /\ 
                            (\A h \in {1..a} : ((h \divides a) /\ (h \divides b) => h <= g))

\* Initial predicate
Init == \/ x = 24
        /\ y \in 1..N
        /\ originalY = y

\* Next state relation
Next ==
    \/ /\ x > y
       /\ x' = x - y
       /\ y' = y
       /\ originalY' = originalY
    \/ /\ x <= y
       /\ x' = x
       /\ y' = y - x
       /\ originalY' = originalY

\* Specification of the system
Spec ==
    Init /\ [][Next]_<<x, y, originalY>> /\ WF_next(<<x, y, originalY>>)

\* Termination property: the algorithm always terminates
Termination == <>(x = 0 \/ y = 0)

=============================================================================