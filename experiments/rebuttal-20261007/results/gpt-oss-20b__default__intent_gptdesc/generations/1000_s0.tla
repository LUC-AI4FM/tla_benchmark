MODULE ResourceAllocator
EXTENDS Naturals

CONSTANTS Clients, Resources

VARIABLES held, request

TypeInvariant ==
    /\ held ∈ [Clients -> SUBSET Resources]
    /\ request ∈ [Clients -> SUBSET Resources]

Init ==
    /\ TypeInvariant
    /\ held = [c ∈ Clients |-> {}]
    /\ request = [c ∈