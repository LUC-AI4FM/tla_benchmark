MODULE TinyGraphSpec
EXTENDS TLC, Sequences

CONSTANTS G, V, N   \* G: set of edges (ordered pairs), V: vertex set, N: natural number

(* Helper operators *)
BoundedSeqHelper(start, len, f) ==
  IF len = 0 THEN <<>>
  ELSE
    f(start) \o BoundedSeqHelper(start+1, len-1, f)

BoundedSequence(n, f) == BoundedSeqHelper(1, n, f)

RandomElement(S) == CHOOSE x \in S : TRUE

TestGraph ==
  { e \in G : TLCEval( e[1] \in V /\ e[2] \in V ) }

(* Variables *)
VARIABLES x, y

(* Assumptions *)
Assumption ==
  Len(BoundedSequence(N, \lambda i : RandomElement(G))) = N

(* Initial state *)
Init == 
  /\ x \in G
  /\ y \in G

(* Next-state relation *)
Next == 
  /\ x' \in G
  /\ y' \in G

(* Invariants *)
TypeInvariant ==
  /\ x \in G
  /\ y \in G

MembershipInvariant ==
  /\ x \in TestGraph
  /\ y \in TestGraph

CardinalityInvariant ==
  TLCEval( Len(BoundedSequence(N, \lambda i : RandomElement(G))) = N )

SafetyInv == TypeInvariant /\ MembershipInvariant

Spec == Init /\ [][Next]_<<x,y>> /\ SafetyInv /\ CardinalityInvariant /\ Assumption

(* Comments: The use of TLCEval forces evaluation in the current context,
   which is necessary to avoid caching issues that would otherwise allow
   the cardinality invariant to be violated. *)

(**************************************************************************)