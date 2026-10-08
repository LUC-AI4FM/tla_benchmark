---------------------------- MODULE euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

VARIABLES pc, u, v, u_ini, v_ini

vars == <<pc, u, v, u_ini, v_ini>>

GCD(x, y) ==
    LET Divisors(n) == {d \in 1..n : n % d = 0}
        CommonDivisors == Divisors(x) \cap Divisors(y)
    IN CHOOSE d \in CommonDivisors : \A e \in CommonDivisors : e <= d

Init ==
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = "a"

Finished == pc = "Done"

SwapOccurs == pc = "a" /\ u # 0 /\ u < v

ActionA ==
    /\ pc = "a"
    /\ IF u # 0
       THEN IF u < v
            THEN /\ u' = v
                 /\ v' = u
                 /\ pc' = "b"
            ELSE /\ u' = u
                 /\ v' = v
                 /\ pc' = "b"
       ELSE /\ Assert(v = GCD(u_ini, v_ini), "GCD assertion failed")
            /\ pc' = "Done"
            /\ u' = u
            /\ v' = v
    /\ UNCHANGED <<u_ini, v_ini>>

ActionB ==
    /\ pc = "b"
    /\ u' = u - v
    /\ v' = v
    /\ pc' = "a"
    /\ UNCHANGED <<u_ini, v_ini>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == ActionA \/ ActionB \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

Invariant == pc = "Done" => v = GCD(u_ini, v_ini)

PossibleCounts ==
    /\ TLCGet("stats").states.distinct = 800
    /\ TLCGet("stats").transitions = 698

=======================================================================