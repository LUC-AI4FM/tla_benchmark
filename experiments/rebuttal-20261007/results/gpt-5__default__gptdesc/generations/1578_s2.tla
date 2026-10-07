------------------------------ MODULE LockFreeDequeDCAS ------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Addr,      \* set of addresses
  Values,    \* set of data values
  N,         \* number of test processes
  LHat,      \* address of left hat (sentinel)
  RHat,      \* address of right hat (sentinel)
  NoVal      \* distinguished non-value (not in Values)

ASSUME /\ LHat \in Addr
       /\ RHat \in Addr
       /\ LHat # RHat
       /\ N \in Nat /\ N > 0
       /\ NoVal \notin Values

Procs == 1..N

ValOpt == Values \cup {NoVal}

Ops == {"pushL","pushR","popL","popR"}
OpsExt == Ops \cup {"idle"}

VARIABLES
  Mem,       \* [Addr -> [val: ValOpt, l: Addr, r: Addr]]
  Free,      \* set of free addresses (never includes LHat or RHat)
  pc,        \* [Procs -> {"T1"}]
  op,        \* [Procs -> OpsExt] last operation executed by each process
  arg,       \* [Procs -> ValOpt] argument value for last push op
  res,       \* [Procs -> ValOpt] result value for last pop op (NoVal if none)
  valBag     \* [Values -> Nat] multiset of values currently in the deque

vars == << Mem, Free, pc, op, arg, res, valBag >>

\* Recursive helpers to compute the set/sequence of nodes/values in the deque
RECURSIVE WalkSeq(_)
WalkSeq(a) ==
  IF a = RHat THEN << >>
  ELSE << Mem[a].val >> \o WalkSeq(Mem[a].r)

RECURSIVE WalkSet(_)
WalkSet(a) ==
  IF a = RHat THEN {}
  ELSE {a} \cup WalkSet(Mem[a].r)

DequeSeq == WalkSeq(Mem[LHat].r)
DequeSet == WalkSet(Mem[LHat].r)

\* Bag helpers
RECURSIVE Count(_, _)
Count(v, s) ==
  IF Len(s) = 0 THEN 0
  ELSE (IF s[1] = v THEN 1 ELSE 0) + Count(v, Tail(s))

ToBag(s) == [ v \in Values |-> Count(v, s) ]

AddBag(b, v) == [ b EXCEPT ![v] = @ + 1 ]
SubBag(b, v) == [ b EXCEPT ![v] = IF @ = 0 THEN 0 ELSE @ - 1 ]

\* Structural predicates
EmptyDeque == (Mem[LHat].r = RHat) /\ (Mem[RHat].l = LHat)

\* Typing and structural invariants
TypeOK ==
  /\ Mem \in [Addr -> [val: ValOpt, l: Addr, r: Addr]]
  /\ Free \subseteq (Addr \ {LHat, RHat})
  /\ pc \in [Procs -> {"T1"}]
  /\ op \in [Procs -> OpsExt]
  /\ arg \in [Procs -> ValOpt]
  /\ res \in [Procs -> ValOpt]
  /\ valBag \in [Values -> Nat]

HatsOK ==
  /\ Mem[LHat].val = NoVal
  /\ Mem[RHat].val = NoVal
  /\ Mem[LHat].l = LHat
  /\ Mem[RHat].r = RHat
  /\ (Mem[LHat].r = RHat) <=> (Mem[RHat].l = LHat)

FreeDisjoint ==
  /\ LHat \notin Free /\ RHat \notin Free
  /\ Free \cap DequeSet = {}

NodeValsOK ==
  /\ \A a \in DequeSet: Mem[a].val \in Values
  /\ \A a \in Free: Mem[a].val = NoVal

BagConsistent ==
  valBag = ToBag(DequeSeq)

Safety ==
  /\ TypeOK
  /\ HatsOK
  /\ FreeDisjoint
  /\ NodeValsOK
  /\ BagConsistent

Init ==
  /\ Mem = [ a \in Addr |->
              IF a = LHat THEN [val |-> NoVal, l |-> LHat, r |-> RHat]
              ELSE IF a = RHat THEN [val |-> NoVal, l |-> LHat, r |-> RHat]
              ELSE [val |-> NoVal, l |-> a, r |-> a] ]
  /\ Free = Addr \ {LHat, RHat}
  /\ pc = [ p \in Procs |-> "T1" ]
  /\ op = [ p \in Procs |-> "idle" ]
  /\ arg = [ p \in Procs |-> NoVal ]
  /\ res = [ p \in Procs |-> NoVal ]
  /\ valBag = [ v \in Values |-> 0 ]

\* DCAS-like atomic paired updates are modeled by single-step actions that read both
\* expected endpoints and update both pointers if they still match the expected values.

PushLeft(p) ==
  \E a \in Free, v \in Values:
    LET first == Mem[LHat].r IN
      /\ IF first = RHat
         THEN
           /\ Mem' = [ Mem EXCEPT
                        ![a]      = [val |-> v, l |-> LHat, r |-> RHat],
                        ![LHat].r = a,
                        ![RHat].l = a ]
           /\ Free' = Free \ {a}
         ELSE
           /\ Mem[first].l = LHat
           /\ Mem' = [ Mem EXCEPT
                        ![a]       = [val |-> v, l |-> LHat, r |-> first],
                        ![LHat].r  = a,
                        ![first].l = a ]
           /\ Free' = Free \ {a}
      /\ valBag' = AddBag(valBag, v)
      /\ op'  = [op EXCEPT ![p] = "pushL"]
      /\ arg' = [arg EXCEPT ![p] = v]
      /\ res' = res
      /\ pc'  = [pc EXCEPT ![p] = "T1"]

PushRight(p) ==
  \E a \in Free, v \in Values:
    LET last == Mem[RHat].l IN
      /\ IF last = LHat
         THEN
           /\ Mem' = [ Mem EXCEPT
                        ![a]       = [val |-> v, l |-> LHat, r |-> RHat],
                        ![LHat].r  = a,
                        ![RHat].l  = a ]
           /\ Free' = Free \ {a}
         ELSE
           /\ Mem[last].r = RHat
           /\ Mem' = [ Mem EXCEPT
                        ![a]       = [val |-> v, l |-> last, r |-> RHat],
                        ![last].r  = a,
                        ![RHat].l  = a ]
           /\ Free' = Free \ {a}
      /\ valBag' = AddBag(valBag, v)
      /\ op'  = [op EXCEPT ![p] = "pushR"]
      /\ arg' = [arg EXCEPT ![p] = v]
      /\ res' = res
      /\ pc'  = [pc EXCEPT ![p] = "T1"]

PopLeft(p) ==
  LET first == Mem[LHat].r IN
    /\ IF first = RHat
       THEN
         /\ Mem' = Mem
         /\ Free' = Free
         /\ valBag' = valBag
         /\ res' = [res EXCEPT ![p] = NoVal]
       ELSE
         LET second == Mem[first].r IN
           IF second = RHat
           THEN
             /\ Mem[RHat].l = first
             /\ Mem' = [ Mem EXCEPT
                          ![LHat].r = RHat,
                          ![RHat].l = LHat,
                          ![first]  = [val |-> NoVal, l |-> first, r |-> first] ]
             /\ Free' = Free \cup {first}
             /\ valBag' = SubBag(valBag, Mem[first].val)
             /\ res' = [res EXCEPT ![p] = Mem[first].val]
           ELSE
             /\ Mem[first].r = second
             /\ Mem[second].l = first
             /\ Mem' = [ Mem EXCEPT
                          ![LHat].r  = second,
                          ![second].l = LHat,
                          ![first]    = [val |-> NoVal, l |-> first, r |-> first] ]
             /\ Free' = Free \cup {first}
             /\ valBag' = SubBag(valBag, Mem[first].val)
             /\ res' = [res EXCEPT ![p] = Mem[first].val]
    /\ op'  = [op EXCEPT ![p] = "popL"]
    /\ arg' = [arg EXCEPT ![p] = NoVal]
    /\ pc'  = [pc EXCEPT ![p] = "T1"]

PopRight(p) ==
  LET last == Mem[RHat].l IN
    /\ IF last = LHat
       THEN
         /\ Mem' = Mem
         /\ Free' = Free
         /\ valBag' = valBag
         /\ res' = [res EXCEPT ![p] = NoVal]
       ELSE
         LET prev == Mem[last].l IN
           IF prev = LHat
           THEN
             /\ Mem[LHat].r = last
             /\ Mem' = [ Mem EXCEPT
                          ![LHat].r = RHat,
                          ![RHat].l = LHat,
                          ![last]   = [val |-> NoVal, l |-> last, r |-> last] ]
             /\ Free' = Free \cup {last}
             /\ valBag' = SubBag(valBag, Mem[last].val)
             /\ res' = [res EXCEPT ![p] = Mem[last].val]
           ELSE
             /\ Mem[prev].r = last
             /\ Mem[last].l = prev
             /\ Mem' = [ Mem EXCEPT
                          ![RHat].l = prev,
                          ![prev].r = RHat,
                          ![last]   = [val |-> NoVal, l |-> last, r |-> last] ]
             /\ Free' = Free \cup {last}
             /\ valBag' = SubBag(valBag, Mem[last].val)
             /\ res' = [res EXCEPT ![p] = Mem[last].val]
    /\ op'  = [op EXCEPT ![p] = "popR"]
    /\ arg' = [arg EXCEPT ![p] = NoVal]
    /\ pc'  = [pc EXCEPT ![p] = "T1"]

Next ==
  \E p \in Procs:
    PushLeft(p) \/ PushRight(p) \/ PopLeft(p) \/ PopRight(p)

Spec ==
  Init /\ [][Next]_vars

\* Liveness: every test process returns to control location T1 infinitely often.
TestLiveness ==
  \A p \in Procs: []<>(pc[p] = "T1")

==============================