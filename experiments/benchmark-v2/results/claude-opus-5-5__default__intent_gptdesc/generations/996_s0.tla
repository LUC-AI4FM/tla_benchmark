---------------------------- MODULE AllocatorRefinement ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Clients,      \* finite set of clients
    Resources,    \* finite set of identical resources (slots)
    MaxClaim      \* policy: a request claiming more than MaxClaim resources is refused

ASSUME /\ IsFiniteSet(Clients)
       /\ IsFiniteSet(Resources)
       /\ MaxClaim \in Nat

-------------------------------------------------------------------------------------
(* Observable variables (shared by specification and implementation)               *)
(*   unsat[c]   : resources requested by c and not yet granted                     *)
(*   alloc[c]   : resources currently held by c                                    *)
(*   claim[c]   : the set of resources named in c's current/last request           *)
(*   refused[c] : TRUE iff c's last request was refused by policy                  *)
(* Internal (implementation-only) variable                                         *)
(*   sched      : scheduler queue of admitted requests, in service order           *)
-------------------------------------------------------------------------------------
VARIABLES unsat, alloc, claim, refused, sched

absVars == <<unsat, alloc, claim, refused>>
vars    == <<unsat, alloc, claim, refused, sched>>

Range(s) == { s[i] : i \in DOMAIN s }

Available == Resources \ UNION { alloc[c] : c \in Clients }

Admissible(S) == Cardinality(S) <= MaxClaim

RECURSIVE SumAlloc(_)
SumAlloc(C) == IF C = {} THEN 0
               ELSE LET c == CHOOSE x \in C : TRUE
                    IN  Cardinality(alloc[c]) + SumAlloc(C \ {c})

=====================================================================================