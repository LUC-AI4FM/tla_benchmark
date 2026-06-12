---- MODULE EuclidsAlgorithm ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm euclid
variables u = u_ini, v = v_ini;
begin
    while (u /= v) do
        if (u > v)
            then u := u - v;
        else
            v := v - u;
end algorithm *)

Init == /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ pc = "start"
        /\ u = u_ini
        /\ v = v_ini

Next ==
    \/ /\ pc = "start"
       /\ pc' = "while_check"
    \/ /\ pc = "while_check"
       /\ u # v
       /\ pc' = "if_cond"
    \/ /\ pc = "while_check"
       /\ u = v
       /\ pc' = "done"
    \/ /\ pc = "if_cond"
       /\ u > v
       /\ u' = u - v
       /\ v' = v
       /\ pc' = "while_check"
    \/ /\ pc = "if_cond"
       /\ u <= v
       /\ u' = u
       /\ v' = v - u
       /\ pc' = "while_check"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, u, v>>
    /\ WF_next(<<pc, u, v>>, Next)

(*--fairness assumptions *)
WF_next(vars, act) == 
    \/ \E vals \in DOMAIN vars : WF_vars(vars, act, {vals})
    \/ \A vals \in DOMAIN vars : SF_vars(vars, act, {vals})

WF_vars(vars, act, S) ==
    /\ \A vals \in S : \A s \in StateSpace : 
        Enabled(act)(s)
        -> <>[]\E s' \in StateSpace : act(s, s') /\ vars[s'] = vals

SF_vars(vars, act, S) ==
    /\ \A vals \in S : \A s \in StateSpace :
        Enabled(act)(s)
        -> <>(\E s' \in StateSpace : act(s, s') /\ vars[s'] = vals)

(*--properties *)
Termination == <>[](pc = "done")

Correctness ==
    LET GCD(a, b) ==
        CHOOSE d \in 1..Min(a, b) :
            /\ a % d = 0
            /\ b % d = 0
            /\ \A k \in 1..Min(a, b) : (a % k = 0 /\ b % k = 0) => k <= d
    IN
        [](pc = "done" => u = GCD(u_ini, v_ini))

(*--expect TLC to count states *)
<< Termination >>_<< pc, u, v >>
<< Correctness >>_<< pc, u, v >>
========================================