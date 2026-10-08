------------------------------- MODULE EuclidGCD -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES x, y, originalY

(*--algorithm EuclidGCD
variables x = 24, y \in 1..N, originalY = y;
begin
    while (x /= 0) /\ (y /= 0)
    do
        if x > y then
            x := x - y;
        else
            y := y - x;
        end if;
    end while;
    print <<originalY, IF x = 0 THEN y ELSE x >>; 
end algorithm*)

Init == /\ x = 24
        /\ originalY \in 1..N
        /\ y = originalY

Next ==
    \/ /\ (x > 0) /\ (y > 0)
       /\ \/ /\ x > y
              /\ x' = x - y
              /\ y' = y
              /\ originalY' = originalY
          \/ /\ x <= y
             /\ x' = x
             /\ y' = y - x
             /\ originalY' = originalY

Spec == Init /\ [][Next]_<<x, y, originalY>>

GCD(a, b) ==
    LET recGCD(x, y) ==
        IF y = 0 THEN x
        ELSE recGCD(y, x % y)
    IN recGCD(a, b)

Termination == <>(x = 0 \/ y = 0)

Correctness == [](x = 0 \/ y = 0) => (IF x = 0 THEN y ELSE x) = GCD(24, originalY)

WF == WF_next(<<x, y, originalY>>)

THEOREM Spec => []Termination

THEOREM Spec => []Correctness
=============================================================================