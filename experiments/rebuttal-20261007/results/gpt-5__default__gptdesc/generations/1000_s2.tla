----------------------------- MODULE ResourceAllocator -----------------------------
EXTENDS TLC, FiniteSets

(*
Simple resource allocator for a finite set of resources and a set of clients.

Constants:
  C: set of clients
  R: set of resources
*)

CONSTANTS C, R

ASSUME /\ C # {}
       /\ R # {}

VARIABLES held, want, req

vars == << held, want, req >>

TypeInv ==
  /\ held \in [C -> SUBSET R]
  /\ want \in [C -> SUBSET R]
  /\ req  \in [C -> SUBSET R]

ReqSubsetWant ==
  \A c \in C: req[c] \subseteq want[c]

MutualExclusion ==
  \A c1, c2 \in C:
    c1 # c2 => (held[c1] \cap held[c2]) = {}

Init ==
  /\ held = [c \in C |-> {}]
  /\ want = [c \in C |-> {}]
  /\ req  = [c \in C |-> {}]

Request(c, S) ==
  /\ c \in C
  /\ S \subseteq R
  /\ S # {}
  /\ held[c] = {}
  /\ want[c] = {}
  /\ req[c]  = {}
  /\ want' = [want EXCEPT ![c] = S]
  /\ req'  = [req  EXCEPT ![c] = S]
  /\ UNCHANGED held

Grant(c, r) ==
  /\ c \in C
  /\ r \in R
  /\ r \in req[c]
  /\ \A d \in C: r \notin held[d]
  /\ held' = [held EXCEPT ![c] = held[c] \cup {r}]
  /\ req'  = [req  EXCEPT ![c] = req[c] \ {r}]
  /\ UNCHANGED want

Return(c, r) ==
  /\ c \in C
  /\ r \in R
  /\ r \in held[c]
  /\ held' = [held EXCEPT ![c] = held[c] \ {r}]
  /\ req'  = IF r \in want[c]
             THEN [req EXCEPT ![c] = req[c] \cup {r}]
             ELSE req
  /\ UNCHANGED want

Complete(c) ==
  /\ c \in C
  /\ want[c] # {}
  /\ req[c] = {}
  /\ want' = [want EXCEPT ![c] = {}]
  /\ UNCHANGED << held, req >>

RequestAct ==
  \E c \in C:
    \E S \in SUBSET R:
      Request(c, S)

GrantAct ==
  \E c \in C:
    \E r \in R:
      Grant(c, r)

ReturnAct ==
  \E c \in C:
    \E r \in R:
      Return(c, r)

CompleteAct ==
  \E c \in C:
    Complete(c)

ReturnAny(c) ==
  \E r \in R: Return(c, r)

Next ==
  RequestAct \/ GrantAct \/ ReturnAct \/ CompleteAct

SpecWeak ==
  Init /\ [][Next]_vars
  /\ \A c \in C: \A r \in R: WF_vars(Grant(c, r))

SpecStrong ==
  Init /\ [][Next]_vars
  /\ \A c \in C: \A r \in R: SF_vars(Grant(c, r))
  /\ \A c \in C: SF_vars(ReturnAny(c))

(*
Liveness properties
*)

EventuallyReturn(c) ==
  [](want[c] = {} => <>(held[c] = {}))

EventuallyObtain(c) ==
  <>(req[c] = {})

InfOftenNoUnsat(c) ==
  []<>(req[c] = {})

Prop_EvReturn_All ==
  \A c \in C: EventuallyReturn(c)

Prop_EvObtain_All ==
  \A c \in C: EventuallyObtain(c)

Prop_InfOftenNoReq_All ==
  \A c \in C: InfOftenNoUnsat(c)

(*
Safety theorems (under either spec, since Next preserves invariants)
*)

THEOREM SafetyUnderWeak ==
  SpecWeak => [](TypeInv /\ ReqSubsetWant /\ MutualExclusion)

THEOREM SafetyUnderStrong ==
  SpecStrong => [](TypeInv /\ ReqSubsetWant /\ MutualExclusion)

(*
Liveness theorems under stronger fairness assumptions
*)

THEOREM LivenessUnderStrong ==
  SpecStrong => (Prop_EvReturn_All /\ Prop_EvObtain_All /\ Prop_InfOftenNoReq_All)

(*
Symmetry expressions (usable with TLC's SYMMETRY)
*)

SymmetryClients == Permutations(C)
SymmetryResources == Permutations(R)

(*
Concrete counterexample value structure (example model values)
These can be used in a TLC model to explore behaviors that may violate
liveness under weak fairness (e.g., starvation).
*)

CE_C == {"c1", "c2"}
CE_R == {"r"}

=============================================================================