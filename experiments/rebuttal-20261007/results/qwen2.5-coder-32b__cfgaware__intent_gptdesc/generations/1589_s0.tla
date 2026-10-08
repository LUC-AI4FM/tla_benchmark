------------------------------- MODULE EuclideanGCD -------------------------------

CONSTANTS MaxInt \* The upper bound for the integers

VARIABLES x, y

(*--algorithm EuclideanGCD
variables x = 1, y = 1;
begin
    while (x /= 0) /\ (y /= 0)
    do
        if x > y then
            x := x - y;
        else
            y := y - x;
        end if;
    end while;
end algorithm*)

Init == \/ \E a, b \in 1..MaxInt : x = a /\ y = b

Next ==
    \/ /\ x > y
       /\ x' = x - y
       /\ y' = y
    \/ /\ y > x
       /\ x' = x
       /\ y' = y - x

Spec == Init /\ [][Next]_<<x, y>>

Termination ==
    <>(x = 0 \/ y = 0)

Invariant ==
    \A s \in StateTrace : 
        /\ (s.x > 0) => s.x \in 1..MaxInt
        /\ (s.y > 0) => s.y \in 1..MaxInt
        /\ GCD(s.x, s.y) = GCD(x, y)

GCD(a, b) ==
    LET recGCD == RECURSIVE gcd(_, _)
                  gcd(m, n) ==
                      IF m = 0 THEN n
                      ELSE IF n = 0 THEN m
                      ELSE IF m > n THEN gcd(m - n, n)
                      ELSE gcd(m, n - m)
    IN recGCD(a, b)

Liveness ==
    [](x /= 0 /\ y /= 0) => <>(x = 0 \/ y = 0)

=============================================================================