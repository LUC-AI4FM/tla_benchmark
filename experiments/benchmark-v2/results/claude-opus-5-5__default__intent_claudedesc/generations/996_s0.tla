------------------------- MODULE AllocatorRefinement -------------------------
(***************************************************************************)
(* Refinement of the simple allocator by the scheduling allocator.        *)
(* Both specs are defined here so the module is self-contained. The       *)
(* scheduling allocator has variables unsat, alloc and sched. The simple   *)
(* allocator has variables unsat and alloc. The refinement mapping is the  *)
(* identity on unsat and alloc, and the extra variable sched is hidden.    *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,  \* unsat[c] is the set of resources c requested but has not received
  alloc,  \* alloc[c] is the set of resources currently allocated to c
  sched   \* order in which clients are scheduled to be served

-------------------------------------------------------------------------
(* Helper operators *)

Range(f) == { f[x] : x \in DOMAIN f }

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

available == Resources \ (UNION { alloc[c] : c \in Clients })

=========================================================================