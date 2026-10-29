---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, y0, pc

vars == <<x, y, y0, pc>>

\* Mathematical definition of GCD
Divides(d, n) == \E k \in 0..n : n = d * k

Divisors(n) == {d \in 1..n : Divides(d, n)}

Max(S) == CHOOSE m \in S : \A s \in S : s <= m

GCD(a, b) == Max(Divisors(a) \cap Divisors(b))

Init ==
    /\ x = 24
    /\ y0 \in 1..N
    /\ y = y0
    /\ pc = "Loop"

\* Repeatedly subtract the smaller value from the larger until one reaches zero
Step ==
    /\ pc = "Loop"
    /\ x # 0
    /\ y # 0
    /\ IF x > y
         THEN /\ x' = x - y
              /\ y' = y
         ELSE /\ y' = y - x
              /\ x' = x
    /\ UNCHANGED <<y0, pc>>

\* One value is zero: the other holds the GCD; print and verify
Finish ==
    /\ pc = "Loop"
    /\ (x = 0 \/ y = 0)
    /\ PrintT(<<"gcd(24, y0) =", x + y, "y0 =", y0>>)
    /\ Assert(x + y = GCD(24, y0), "Computed GCD is incorrect")
    /\ pc' = "Done"
    /\ UNCHANGED <<x, y, y0>>

\* Allow stuttering once finished to avoid deadlock
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ x \in 0..24
    /\ y \in 0..N
    /\ y0 \in 1..N
    /\ pc \in {"Loop", "Done"}

Correctness == (pc = "Done") => (x + y = GCD(24, y0))

Termination == <>(pc = "Done")

=============================================================================