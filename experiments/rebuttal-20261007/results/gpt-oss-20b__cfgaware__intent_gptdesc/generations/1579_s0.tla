\*======================================================================
\* MODULE TokenRing
\*
\* Specification of a token circulation algorithm on a unidirectional ring.
\* The module defines the constants, variables and operators required by
\* the configuration: Spec, N, SomeoneHoldsToken, EventuallyJustOneHoldsToken.
\*======================================================================

EXTENDS Naturals, Sequences, Integers

CONSTANTS N, K

(*--------------------------------------------------------------------
  Predecessor and Successor functions on a ring of size N
--------------------------------------------------------------------*)
Predecessor(i) == IF i = 0 THEN N-1 ELSE i - 1
Successor(i)   == Mod(i + 1, N)

(*--------------------------------------------------------------------
  State variable: counters[i] is the local counter of process i.
--------------------------------------------------------------------*)
VARIABLE counters

(*--------------------------------------------------------------------
  Initial state: all counters are 0 except process 0 which has value 1.
  This guarantees that at least one token holder exists initially.
--------------------------------------------------------------------*)
Init ==
  /\ \A i \in 0..N-1 : counters[i] = 0
  /\ counters[0] = 1

(*--------------------------------------------------------------------
  Token passing action for process i.  
  The process holds the token iff its counter differs from that of its
  predecessor.  When it passes the token, it copies its own value to
  its successor and adopts its predecessor's value.
--------------------------------------------------------------------*)
TokenPass(i) ==
  /\ i \in 0..N-1
  /\ counters[i] # counters[Predecessor(i)]
  /\ LET p == Predecessor(i)
        s == Successor(i)
      IN
         /\ counters' = [counters EXCEPT ![s] = counters[i], ![i] = counters[p]]

(*--------------------------------------------------------------------
  Next-state relation: any process that holds the token may perform
  a token-passing step.
--------------------------------------------------------------------*)
Next ==
  \E i \in 0..N-1 : TokenPass(i)

(*--------------------------------------------------------------------
  The complete specification.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_counters

(*--------------------------------------------------------------------
  Safety property: at least one process holds the token in every state.
--------------------------------------------------------------------*)
SomeoneHoldsToken ==
   \E i \in 0..N-1 : counters[i] # counters[Predecessor(i)]

(*--------------------------------------------------------------------
  Predicate for exactly one holder of the token.
--------------------------------------------------------------------*)
ExactlyOneHolder ==
   (\E i \in 0..N-1 :
        /\ counters[i] # counters[Predecessor(i)]
        /\ \A j \in 0..N-1 : (j /= i) => counters[j] = counters[Predecessor(j)] )

(*--------------------------------------------------------------------
  Liveness property: eventually the system reaches a regime where
  exactly one process holds the token and remains in that regime.
--------------------------------------------------------------------*)
EventuallyJustOneHoldsToken == \Diamond \Box ExactlyOneHolder

(*--------------------------------------------------------------------
  Assumption about constants (used for verification).
--------------------------------------------------------------------*)
THEOREM K_gt_N == K > N

============================================================================)