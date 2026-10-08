------------------------------- MODULE EuclidGCD -------------------------------

CONSTANTS MaxValue \* Assumed to be 20 for this problem

VARIABLES x, y

(*--algorithm EuclidGCD
variables x = 1, y = 1;
begin
    Init:
        with
            a \in 1..MaxValue,
            b \in 1..MaxValue
        do
            x := a;
            y := b;
        endwith;
    while x # 0 do
        if x < y then
            x := x + y; \* Swap x and y by adding y to x
            y := x - y;
            x := x - y;
        else
            x := x - y;
        end if;
    end while;
end algorithm;*)

Spec == Init /\ [][Next]_<<x, y>> /\ WF_next(<<x, y>>)

Init == \/ x \in 1..MaxValue
        \/ y \in 1..MaxValue

Next ==
    \/ /\ x # 0
       /\ (x < y -> (x' = x + y) /\ (y' = x))
          \/ (x >= y -> (x' = x - y) /\ (y' = y))

WF_next(vars) == WF_vars(Next, vars)

Termination ==
    <>[](x = 0)

Invariant ==
    \A a \in 1..MaxValue, b \in 1..MaxValue :
        <>(/\ x = GCD(a, b)
            /\ y = GCD(a, b))

GCD(m, n) == CHOOSE d \in 1..Min(m, n) : (m % d = 0) /\ (n % d = 0)

=============================================================================