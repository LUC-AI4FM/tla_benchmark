------------------------------- MODULE ResourceAllocator -------------------------------

EXTENDS TLC, FiniteSets

(*
  A simple resource allocator:
  - Clients issue a (nonempty) request only when they hold no resources and have no outstanding request.
  - Requests may be partially fulfilled over time: each Grant assigns one requested free resource.
  - Clients may return any nonempty subset of held resources at any time, even before a request is fully satisfied.
  - Two temporal specs with different fairness assumptions are provided.
  - Safety and liveness properties are stated.
  - A symmetry expression and a concrete counterexample value structure are included.
*)

CONSTANTS
  Clients,    \* finite, nonempty set of clients
  Resources   \* finite, possibly empty set of resources

VARIABLES
  held,       \* [Clients -> SUBSET Resources]: resources currently held by each client
  req         \* [Clients -> SUBSET Resources]: current unsatisfied request of each client

vars == << held, req >>

=============================================================================