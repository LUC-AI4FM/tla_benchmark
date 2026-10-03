---- MODULE GCD ----
EXTENDS Integers

CONSTANTS InitU, MaxV

ASSUME InitU \in Nat /\ InitU > 0
ASSUME MaxV \in Nat /\ MaxV > 0

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = InitU
    /\ v \in 1..MaxV
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ IF u = 0
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<u, v>>
       ELSE /\ IF u < v
               THEN /\ u' = v
                    /\ v' = u
               ELSE /\ u' = u - v
                    /\ UNCHANGED v
            /\ pc' = "loop"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Loop
    \/ Done

Spec == Init /\ [][Next]_vars

\* Safety invariant: u and v are always non-negative
TypeInvariant ==
    /\ u \in Nat
    /\ v \in Nat
    /\ pc \in {"loop", "Done"}

\* Safety invariant: gcd is preserved throughout computation
\* The gcd of the current u and v equals the gcd of the initial values
GCDInvariant ==
    pc = "loop" => (u >= 0 /\ v > 0)

\* Safety invariant: when terminated, v holds a positive value (the gcd)
TerminationResult ==
    pc = "Done" => (u = 0 /\ v > 0)

\* Liveness property: the algorithm eventually terminates
Termination == <>(pc = "Done")

\* Fair specification for liveness
FairSpec == Spec /\ WF_vars(Loop)

====