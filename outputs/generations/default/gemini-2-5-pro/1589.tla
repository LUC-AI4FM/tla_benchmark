----------------------------- MODULE Euclid -----------------------------
EXTENDS Integers, TLC

CONSTANT MaxNum

VARIABLES 
    \* The initial values for which to compute the GCD.
    u_ini, v_ini,
    
    \* The working variables for the algorithm.
    u, v,
    
    \* The program counter.
    pc

vars == <<u_ini, v_ini, u, v, pc>>

-----------------------------------------------------------------------------
\* Definition of the mathematical Greatest Common Divisor (GCD) operator.
\* This is used in the Correctness assertion, not by the algorithm itself.
RECURSIVE GCD(_, _)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

-----------------------------------------------------------------------------
\* The PlusCal algorithm translated to TLA+.

\* --algorithm Euclid
\* variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u, v;
\* begin
\*   E:
\*     u := u_ini;
\*     v := v_ini;
\*     while u /= v do
\*       if u > v then
\*         u := u - v;
\*       else
\*         v := v - u;
\*       end if;
\*     end while;
\*     assert u = GCD(u_ini, v_ini);
\* end algorithm;

\* The Init predicate defines the set of initial states.
\* We choose two positive integers and set up the algorithm's variables.
Init ==
    /\ \E m, n \in 1..MaxNum :
        /\ u_ini = m
        /\ v_ini = n
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = "Euclid"

\* The actions defining the steps of the algorithm.
\* Case where u is greater than v.
Euclid_gt ==
    /\ pc = "Euclid"
    /\ u > v
    /\ u' = u - v
    /\ v' = v
    /\ pc' = "Euclid"
    /\ UNCHANGED <<u_ini, v_ini>>

\* Case where v is greater than u.
Euclid_lt ==
    /\ pc = "Euclid"
    /\ u < v
    /\ v' = v - u
    /\ u' = u
    /\ pc' = "Euclid"
    /\ UNCHANGED <<u_ini, v_ini>>

\* The algorithm terminates when u and v are equal.
Euclid_terminate ==
    /\ pc = "Euclid"
    /\ u = v
    /\ pc' = "Done"
    /\ UNCHANGED <<u, v, u_ini, v_ini>>
    
\* The Next-state relation.
Next ==
    \/ Euclid_gt
    \/ Euclid_lt
    \/ Euclid_terminate
    \/ /\ pc = "Done"  \* Stuttering step for the terminal state.
       /\ UNCHANGED vars

-----------------------------------------------------------------------------
\* The complete specification.
\* Init defines the initial state.
\* [][Next]_vars means that every step is either a Next step or leaves vars unchanged.
\* WF_vars(Next) is a weak fairness condition on the Next action, ensuring
\* that if an action is continuously enabled, it will eventually be taken.
\* This guarantees termination.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Temporal properties to be checked by the model checker.

\* Safety Property: Correctness
\* Asserts that if the algorithm terminates, the resulting value of u (or v)
\* is indeed the greatest common divisor of the initial inputs.
Correctness == pc = "Done" => u = GCD(u_ini, v_ini)

\* Liveness Property: Termination
\* Asserts that the algorithm eventually reaches the "Done" state.
Termination == <> (pc = "Done")

\* A type invariant to ensure variables stay within their expected domains.
\* While not explicitly requested, this is good practice for model checking.
TypeOK ==
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u \in 1..MaxNum
    /\ v \in 1..MaxNum
    /\ pc \in {"Euclid", "Done"}

=============================================================================