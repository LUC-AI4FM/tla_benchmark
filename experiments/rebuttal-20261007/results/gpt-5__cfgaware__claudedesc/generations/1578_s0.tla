----------------------------- MODULE Snark -----------------------------
EXTENDS Naturals, TLC

CONSTANTS
  Address, \* set of memory addresses (nodes)
  Dummy,   \* distinguished sentinel address in Address
  Procs,   \* set of process identifiers
  Val,     \* set of values pushed into the deque
  defaultInitValue

(*
  We model a doubly-linked deque in shared memory anchored at Dummy.
  Each node is a record with fields l (left), r (right), and v (value).
  The distinguished value NoneVal represents the absence of a logical value
  in a node (e.g., for free-list nodes). It is defined as defaultInitValue
  and is assumed (by the model) not to be in Val.
*)
NoneVal == defaultInitValue

Value == Val \cup {NoneVal}

NodeType == [l: Address, r: Address, v: Value]

VARIABLES
  Mem,       \* Address -> NodeType
  freeList,  \* subset of Address \ {Dummy}
  LeftHat,   \* anchored at Dummy (never changes)
  RightHat,  \* anchored at Dummy (never changes)
  rVal,      \* [Procs -> (Value \cup {"empty","full"})]
  valBag,    \* multiset (bag) of Val: function Val -> Nat
  pc         \* [Procs -> {"T1"}] control point label

vars == << Mem, freeList, LeftHat, RightHat, rVal, valBag, pc >>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

IsEmpty == /\ Mem[Dummy].l = Dummy
           /\ Mem[Dummy].r = Dummy

RightMost == Mem[Dummy].r
LeftMost  == Mem[Dummy].l

EmptyBag == [v \in Val |-> 0]
AddToBag(b, v) == [b EXCEPT ![v] = b[v] + 1]
RemFromBag(b, v) == [b EXCEPT ![v] = b[v] - 1]

(*
  DCAS "macros" capture the compare phase for two fields.
  They are used as guards before performing the corresponding atomic updates.
*)
DCASrr(a1, old1, a2, old2) == /\ Mem[a1].r = old1 /\ Mem[a2].r = old2
DCASll(a1, old1, a2, old2) == /\ Mem[a1].l = old1 /\ Mem[a2].l = old2
DCASrl(a1, old1, a2, old2) == /\ Mem[a1].r = old1 /\ Mem[a2].l = old2

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ Mem = [a \in Address |->
              IF a = Dummy
                THEN [l |-> Dummy, r |-> Dummy, v |-> NoneVal]
                ELSE [l |-> a,     r |-> a,     v |-> NoneVal]]
  /\ freeList = Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal = [p \in Procs |-> defaultInitValue]
  /\ valBag = EmptyBag
  /\ pc = [p \in Procs |-> "T1"]

(***************************************************************************)
(* Deque operations (one-step, abstracting retries via nondeterminism)     *)
(***************************************************************************)

PushRight(p) ==
  \E v \in Val:
    IF freeList = {} THEN
      /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag >>
      /\ rVal' = [rVal EXCEPT ![p] = "full"]
      /\ pc' = [pc EXCEPT ![p] = "T1"]
    ELSE
      \E a \in freeList:
        LET right == RightMost IN
        IF right = Dummy THEN
          /\ DCASrl(Dummy, Dummy, Dummy, Dummy)
          /\ Mem' =
              [Mem EXCEPT
                ![a]      = [l |-> Dummy, r |-> Dummy, v |-> v],
                ![Dummy].r = a,
                ![Dummy].l = a]
        ELSE
          /\ DCASrr(right, Dummy, Dummy, right)
          /\ Mem' =
              [Mem EXCEPT
                ![a]        = [l |-> right, r |-> Dummy, v |-> v],
                ![right].r  = a,
                ![Dummy].r  = a]
        /\ freeList' = freeList \ {a}
        /\ valBag' = AddToBag(valBag, v)
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ UNCHANGED << LeftHat, RightHat >>
        /\ pc' = [pc EXCEPT ![p] = "T1"]

PushLeft(p) ==
  \E v \in Val:
    IF freeList = {} THEN
      /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag >>
      /\ rVal' = [rVal EXCEPT ![p] = "full"]
      /\ pc' = [pc EXCEPT ![p] = "T1"]
    ELSE
      \E a \in freeList:
        LET left == LeftMost IN
        IF left = Dummy THEN
          /\ DCASrl(Dummy, Dummy, Dummy, Dummy)
          /\ Mem' =
              [Mem EXCEPT
                ![a]      = [l |-> Dummy, r |-> Dummy, v |-> v],
                ![Dummy].r = a,
                ![Dummy].l = a]
        ELSE
          /\ DCASll(left, Dummy, Dummy, left)
          /\ Mem' =
              [Mem EXCEPT
                ![a]       = [l |-> Dummy, r |-> left,  v |-> v],
                ![left].l  = a,
                ![Dummy].l = a]
        /\ freeList' = freeList \ {a}
        /\ valBag' = AddToBag(valBag, v)
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ UNCHANGED << LeftHat, RightHat >>
        /\ pc' = [pc EXCEPT ![p] = "T1"]

PopRight(p) ==
  IF IsEmpty THEN
    /\ UNCHANGED << Mem, freeList, valBag, LeftHat, RightHat >>
    /\ rVal' = [rVal EXCEPT ![p] = "empty"]
    /\ pc' = [pc EXCEPT ![p] = "T1"]
  ELSE
    LET right == RightMost IN
    IF Mem[right].l = Dummy THEN
      \* Singleton case: both ends point to the same node
      /\ DCASrl(Dummy, right, Dummy, right)
      /\ TLC!Assert(valBag[Mem[right].v] > 0, "PopRight: value not in bag")
      /\ Mem' =
          [Mem EXCEPT
            ![Dummy].r = Dummy,
            ![Dummy].l = Dummy,
            ![right].v = NoneVal]
      /\ freeList' = freeList \cup {right}
      /\ valBag' = RemFromBag(valBag, Mem[right].v)
      /\ rVal' = [rVal EXCEPT ![p] = Mem[right].v]
      /\ UNCHANGED << LeftHat, RightHat >>
      /\ pc' = [pc EXCEPT ![p] = "T1"]
    ELSE
      LET leftOfRight == Mem[right].l IN
      /\ DCASrr(Dummy, right, leftOfRight, right)
      /\ TLC!Assert(valBag[Mem[right].v] > 0, "PopRight: value not in bag")
      /\ Mem' =
          [Mem EXCEPT
            ![Dummy].r        = leftOfRight,
            ![leftOfRight].r  = Dummy,
            ![right].v        = NoneVal]
      /\ freeList' = freeList \cup {right}
      /\ valBag' = RemFromBag(valBag, Mem[right].v)
      /\ rVal' = [rVal EXCEPT ![p] = Mem[right].v]
      /\ UNCHANGED << LeftHat, RightHat >>
      /\ pc' = [pc EXCEPT ![p] = "T1"]

PopLeft(p) ==
  IF IsEmpty THEN
    /\ UNCHANGED << Mem, freeList, valBag, LeftHat, RightHat >>
    /\ rVal' = [rVal EXCEPT ![p] = "empty"]
    /\ pc' = [pc EXCEPT ![p] = "T1"]
  ELSE
    LET left == LeftMost IN
    IF Mem[left].r = Dummy THEN
      \* Singleton case: both ends point to the same node
      /\ DCASrl(Dummy, left, Dummy, left)
      /\ TLC!Assert(valBag[Mem[left].v] > 0, "PopLeft: value not in bag")
      /\ Mem' =
          [Mem EXCEPT
            ![Dummy].r = Dummy,
            ![Dummy].l = Dummy,
            ![left].v  = NoneVal]
      /\ freeList' = freeList \cup {left}
      /\ valBag' = RemFromBag(valBag, Mem[left].v)
      /\ rVal' = [rVal EXCEPT ![p] = Mem[left].v]
      /\ UNCHANGED << LeftHat, RightHat >>
      /\ pc' = [pc EXCEPT ![p] = "T1"]
    ELSE
      LET rightOfLeft == Mem[left].r IN
      /\ DCASll(Dummy, left, rightOfLeft, left)
      /\ TLC!Assert(valBag[Mem[left].v] > 0, "PopLeft: value not in bag")
      /\ Mem' =
          [Mem EXCEPT
            ![Dummy].l       = rightOfLeft,
            ![rightOfLeft].l = Dummy,
            ![left].v        = NoneVal]
      /\ freeList' = freeList \cup {left}
      /\ valBag' = RemFromBag(valBag, Mem[left].v)
      /\ rVal' = [rVal EXCEPT ![p] = Mem[left].v]
      /\ UNCHANGED << LeftHat, RightHat >>
      /\ pc' = [pc EXCEPT ![p] = "T1"]

Step(p) ==
  PushRight(p) \/ PushLeft(p) \/ PopRight(p) \/ PopLeft(p)

Next ==
  \E p \in Procs : Step(p)

Spec ==
  Init /\ [][Next]_vars

(***************************************************************************)
(* Optional properties                                                     *)
(***************************************************************************)

TypeOK ==
  /\ Mem \in [Address -> NodeType]
  /\ freeList \subseteq Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal \in [Procs -> (Value \cup {"empty","full"})]
  /\ valBag \in [Val -> Nat]
  /\ pc \in [Procs -> {"T1"}]

Liveness ==
  \A p \in Procs : [](<> pc[p] = "T1")

(***************************************************************************)
(* Symmetry helpers (for model configuration convenience)                  *)
(***************************************************************************)

SymmetryAddrs == Address \ {Dummy}
SymmetryProcs == Procs

=============================================================================