------------------------------ MODULE LockFreeDeque ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Lock-Free Double-Ended Queue (Deque) with DCAS, linked memory pool, and a test harness.

  Required externally bound constants:
    - Val: a finite, non-empty set of storable values
    - defaultInitValue: an element used as a default placeholder value

  Required externally bound operator:
    - Spec: the system behavior

  This specification models:
    - A doubly-linked circular list with a distinguished sentinel address Sent = 0
    - A finite pool of addresses (nodes) from which the deque allocates/frees nodes
    - Four concurrent operations: PushL, PushR, PopL, PopR
    - DCAS as the atomic synchronization primitive (abstractly captured)
    - A ghost abstract sequence Abs of nodes to ensure linearizability and queue semantics
    - A simple randomized test harness with two processes
*)

CONSTANTS
  Val,
  defaultInitValue

(***************************************************************************)
(* Derived finite domains and helper operators                              *)
(***************************************************************************)

(*
  Allocate a finite pool of node addresses sized as a function of |Val|.
  The pool size is intentionally larger than |Val| to reduce artificial exhaustion.
*)
CardVal  == Cardinality(Val)
NNodes   == 2*CardVal + 2
Sent     == 0
Addr     == {Sent} \cup (1..NNodes)
Nodes    == Addr \ {Sent}

Pids     == 1..2
Ops      == {"PushL", "PushR", "PopL", "PopR"}
Statuses == {"idle", "okay", "empty", "full"}

(*
  Sequence/set helpers
*)
SeqToSet(S) == { S[i] : i \in 1..Len(S) }

InSeq(S, a) ==
  \E i \in 1..Len(S) : S[i] = a

Index(S, a) ==
  IF InSeq(S, a)
    THEN CHOOSE i \in 1..Len(S) : S[i] = a
    ELSE 0

LeftEnd(S) ==
  IF Len(S) = 0 THEN Sent ELSE S[1]

RightEnd(S) ==
  IF Len(S) = 0 THEN Sent ELSE S[Len(S)]

(*
  Rebuild the concrete next/prev pointers from a sequence of distinct nodes S
  that represents the deque content from left to right (excluding the sentinel).
*)
NextFromSeq(S) ==
  [ a \in Addr |->
      IF a = Sent THEN
        IF Len(S) = 0 THEN Sent ELSE S[1]
      ELSE IF InSeq(S, a) THEN
        LET i == Index(S, a) IN IF i = Len(S) THEN Sent ELSE S[i+1]
      ELSE
        a
  ]

PrevFromSeq(S) ==
  [ a \in Addr |->
      IF a = Sent THEN
        IF Len(S) = 0 THEN Sent ELSE S[Len(S)]
      ELSE IF InSeq(S, a) THEN
        LET i == Index(S, a) IN IF i = 1 THEN Sent ELSE S[i-1]
      ELSE
        a
  ]

(*
  Abstract DCAS predicate: succeeds iff both compared locations currently
  match the provided expected values; the update itself is part of the atomic step.
  We use it as an annotation to emphasize the use of DCAS in each operation.
*)
DCAS(loc1, exp1, loc2, exp2) == (loc1 = exp1) /\ (loc2 = exp2)

(***************************************************************************)
(* State variables                                                          *)
(***************************************************************************)

VARIABLES
  next,        \* [Addr -> Addr] concrete next pointer field
  prev,        \* [Addr -> Addr] concrete prev pointer field
  data,        \* [Addr -> Val]  stored value per node address
  Free,        \* SUBSET Nodes: free-address pool
  Abs,         \* Seq(Nodes): abstract deque contents (node sequence)
  ret,         \* [Pids -> Statuses] last-completion status per process
  rval,        \* [Pids -> Val] returned value for last Pop (or default)
  opKind,      \* [Pids -> (Ops \cup {"Idle"})] last operation kind per process
  poppedNode,  \* [Pids -> Addr] last popped node id (Sent if none)
  histPopped   \* SUBSET Nodes: nodes popped since last time they were re-pushed

vars == << next, prev, data, Free, Abs, ret, rval, opKind, poppedNode, histPopped >>

(***************************************************************************)
(* Initialization                                                           *)
(***************************************************************************)

Init ==
  /\ Abs = << >>
  /\ next = NextFromSeq(Abs)
  /\ prev = PrevFromSeq(Abs)
  /\ data = [a \in Addr |-> defaultInitValue]
  /\ Free = Nodes
  /\ ret  = [p \in Pids |-> "idle"]
  /\ rval = [p \in Pids |-> defaultInitValue]
  /\ opKind = [p \in Pids |-> "Idle"]
  /\ poppedNode = [p \in Pids |-> Sent]
  /\ histPopped = {}

(***************************************************************************)
(* Operations (each abstractly uses DCAS on relevant pointer pairs)         *)
(***************************************************************************)

PushL(p) ==
  LET oldFirst == LeftEnd(Abs) IN
  IF Free = {} THEN
    /\ ret'  = [ret EXCEPT ![p] = "full"]
    /\ UNCHANGED << next, prev, data, Free, Abs, rval, opKind, poppedNode, histPopped >>
  ELSE
    \E x \in Free, v \in Val :
      \E e1 \in Addr, e2 \in Addr :
        /\ e1 = next[Sent]
        /\ e2 = (IF oldFirst = Sent THEN Sent ELSE prev[oldFirst])
        /\ DCAS(next[Sent], e1, (IF oldFirst = Sent THEN prev[Sent] ELSE prev[oldFirst]), e2)
        /\ Abs'  = << x >> \o Abs
        /\ data' = [data EXCEPT ![x] = v]
        /\ Free' = Free \ {x}
        /\ next' = NextFromSeq(Abs')
        /\ prev' = PrevFromSeq(Abs')
        /\ ret'  = [ret EXCEPT ![p] = "okay"]
        /\ rval' = [rval EXCEPT ![p] = defaultInitValue]
        /\ opKind' = [opKind EXCEPT ![p] = "PushL"]
        /\ poppedNode' = poppedNode
        /\ histPopped' = histPopped \ {x}

PushR(p) ==
  LET oldLast == RightEnd(Abs) IN
  IF Free = {} THEN
    /\ ret'  = [ret EXCEPT ![p] = "full"]
    /\ UNCHANGED << next, prev, data, Free, Abs, rval, opKind, poppedNode, histPopped >>
  ELSE
    \E x \in Free, v \in Val :
      \E e1 \in Addr, e2 \in Addr :
        /\ e1 = prev[Sent]
        /\ e2 = (IF oldLast = Sent THEN Sent ELSE next[oldLast])
        /\ DCAS(prev[Sent], e1, (IF oldLast = Sent THEN next[Sent] ELSE next[oldLast]), e2)
        /\ Abs'  = Abs \o << x >>
        /\ data' = [data EXCEPT ![x] = v]
        /\ Free' = Free \ {x}
        /\ next' = NextFromSeq(Abs')
        /\ prev' = PrevFromSeq(Abs')
        /\ ret'  = [ret EXCEPT ![p] = "okay"]
        /\ rval' = [rval EXCEPT ![p] = defaultInitValue]
        /\ opKind' = [opKind EXCEPT ![p] = "PushR"]
        /\ poppedNode' = poppedNode
        /\ histPopped' = histPopped \ {x}

PopL(p) ==
  IF Len(Abs) = 0 THEN
    /\ ret'  = [ret EXCEPT ![p] = "empty"]
    /\ rval' = [rval EXCEPT ![p] = defaultInitValue]
    /\ opKind' = [opKind EXCEPT ![p] = "PopL"]
    /\ UNCHANGED << next, prev, data, Free, Abs, poppedNode, histPopped >>
  ELSE
    LET x == Abs[1]
        v == data[x]
        oldFirst == LeftEnd(Abs)
    IN
    \E e1 \in Addr, e2 \in Addr :
      /\ e1 = next[Sent]
      /\ e2 = prev[x]
      /\ DCAS(next[Sent], e1, prev[x], e2)
      /\ Abs'  = IF Len(Abs) = 1 THEN << >> ELSE SubSeq(Abs, 2, Len(Abs))
      /\ Free' = Free \cup {x}
      /\ next' = NextFromSeq(Abs')
      /\ prev' = PrevFromSeq(Abs')
      /\ data' = data
      /\ ret'  = [ret EXCEPT ![p] = "okay"]
      /\ rval' = [rval EXCEPT ![p] = v]
      /\ opKind' = [opKind EXCEPT ![p] = "PopL"]
      /\ poppedNode' = [poppedNode EXCEPT ![p] = x]
      /\ histPopped' = histPopped \cup {x}

PopR(p) ==
  IF Len(Abs) = 0 THEN
    /\ ret'  = [ret EXCEPT ![p] = "empty"]
    /\ rval' = [rval EXCEPT ![p] = defaultInitValue]
    /\ opKind' = [opKind EXCEPT ![p] = "PopR"]
    /\ UNCHANGED << next, prev, data, Free, Abs, poppedNode, histPopped >>
  ELSE
    LET x == Abs[Len(Abs)]
        v == data[x]
        oldLast == RightEnd(Abs)
    IN
    \E e1 \in Addr, e2 \in Addr :
      /\ e1 = prev[Sent]
      /\ e2 = next[x]
      /\ DCAS(prev[Sent], e1, next[x], e2)
      /\ Abs'  = IF Len(Abs) = 1 THEN << >> ELSE SubSeq(Abs, 1, Len(Abs)-1)
      /\ Free' = Free \cup {x}
      /\ next' = NextFromSeq(Abs')
      /\ prev' = PrevFromSeq(Abs')
      /\ data' = data
      /\ ret'  = [ret EXCEPT ![p] = "okay"]
      /\ rval' = [rval EXCEPT ![p] = v]
      /\ opKind' = [opKind EXCEPT ![p] = "PopR"]
      /\ poppedNode' = [poppedNode EXCEPT ![p] = x]
      /\ histPopped' = histPopped \cup {x}

(***************************************************************************)
(* Randomized concurrent harness                                            *)
(***************************************************************************)

Step ==
  \E p \in Pids :
    PushL(p) \/ PushR(p) \/ PopL(p) \/ PopR(p)

Next == Step

(***************************************************************************)
(* Temporal specification                                                   *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants and properties (for model checking)                           *)
(***************************************************************************)

(*
  Type correctness
*)
TypeInv ==
  /\ next \in [Addr -> Addr]
  /\ prev \in [Addr -> Addr]
  /\ data \in [Addr -> Val]
  /\ Free \subseteq Nodes
  /\ Abs \in Seq(Nodes)
  /\ \A i, j \in 1..Len(Abs) : i # j => Abs[i] # Abs[j]
  /\ ret \in [Pids -> Statuses]
  /\ rval \in [Pids -> Val]
  /\ opKind \in [Pids -> (Ops \cup {"Idle"})]
  /\ poppedNode \in [Pids -> Addr]
  /\ histPopped \subseteq Nodes

(*
  Concrete list corresponds exactly to the abstract order Abs
*)
DequeShape ==
  /\ next = NextFromSeq(Abs)
  /\ prev = PrevFromSeq(Abs)

(*
  No lost or duplicated nodes: nodes in use equal exactly Abs's set
*)
NoLostNoDupNodes ==
  /\ (Nodes \ Free) = SeqToSet(Abs)
  /\ Cardinality(SeqToSet(Abs)) = Len(Abs)

(*
  Proper empty detection (event-level): whenever a Pop returns "empty" in this step, Abs was empty.
  For state-level checking, users may inspect steps; here we provide an action predicate.
*)
PopEmptyEvent(p) ==
  (opKind'[p] \in {"PopL", "PopR"}) /\ (ret'[p] = "empty") /\ (Len(Abs) = 0)

(*
  No duplicate returns of the same pushed instance without a re-push:
  a node can only be popped once until it is re-pushed.
  We track histPopped to ensure popped nodes are not currently in Abs.
*)
NoDuplicateReturnsInv ==
  /\ histPopped \cap SeqToSet(Abs) = {}
  /\ histPopped \subseteq Nodes

(*
  Proper empty detection (state-level approximation for checking right after a Pop-empty step):
  If the most recent operation of any process is Pop* with "empty", then Abs must be empty
  in that state (i.e., at the moment of the return).
*)
ProperEmptyDetectionInv ==
  \A p \in Pids :
    (opKind[p] \in {"PopL", "PopR"} /\ ret[p] = "empty") => Len(Abs) = 0

(***************************************************************************)
(* THEOREMS (optional; TLC can check invariants by configuration)           *)
(***************************************************************************)

THEOREM Init => TypeInv

=============================================================================