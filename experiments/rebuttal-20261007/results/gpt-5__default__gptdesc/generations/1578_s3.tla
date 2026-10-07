------------------------------ MODULE LockFreeDeque ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  PROC,          \* Set of test processes
  VALS,          \* Set of storable values
  ADDR,          \* Set of addresses (includes a null-like address)
  LeftHat,       \* Address of left hat sentinel
  RightHat,      \* Address of right hat sentinel
  NullAddr,      \* Distinguished null-like address in ADDR
  NoVal          \* Distinguished value not in VALS, used for "no return"/empty pops

ASSUME
  /\ LeftHat \in ADDR /\ RightHat \in ADDR /\ NullAddr \in ADDR
  /\ LeftHat # RightHat
  /\ LeftHat # NullAddr /\ RightHat # NullAddr
  /\ NoVal \notin VALS

(*
  Informal intent:
  - A lock-free double-ended queue (deque) with Detlefs-style paired pointer updates
    that emulate DCAS on (prev,next) edges adjacent to the sentinels.
  - Shared state includes:
      * mem: ADDR -> [prev, next, val, live]
      * free: pool of unallocated addresses
      * valBag: multiset of logical deque contents (as VALS -> Nat)
      * pc, ret: per-process control and return variables
  - The algorithm models high-level atomic pushLeft, pushRight, popLeft, popRight
    steps that perform "paired" updates on adjacent pointers (the two ends),
    with preconditions that both compared locations match, akin to DCAS.
  - Test processes repeatedly and nondeterministically choose one of the four
    operations; the liveness property states every test process returns to T1
    infinitely often.
*)

\* Node record fields: prev, next: ADDR; val: VALS \cup {NoVal}; live: BOOLEAN
NodeType ==
  [ prev: ADDR,
    next: ADDR,
    val:  VALS \cup {NoVal},
    live: BOOLEAN ]

IsDataNode(a) == (a # LeftHat) /\ (a # RightHat)
LiveData(a)   == IsDataNode(a) /\ mem[a].live

VARIABLES
  mem,       \* memory: ADDR -> NodeType
  free,      \* freelist: subset of ADDR \ {LeftHat,RightHat}
  valBag,    \* bag of values: VALS -> Nat
  pc,        \* per-process control location: only "T1"
  ret        \* per-process last returned value (VALS \cup {NoVal})

vars == << mem, free, valBag, pc, ret >>

Init ==
  /\ mem = [ a \in ADDR |->
              IF a = LeftHat THEN
                [prev |-> NullAddr, next |-> RightHat, val |-> NoVal, live |-> TRUE]
              ELSE IF a = RightHat THEN
                [prev |-> LeftHat, next |-> NullAddr, val |-> NoVal, live |-> TRUE]
              ELSE
                [prev |-> NullAddr, next |-> NullAddr, val |-> NoVal, live |-> FALSE] ]
  /\ free = ADDR \ {LeftHat, RightHat}
  /\ valBag = [ v \in VALS |-> 0 ]
  /\ pc = [ p \in PROC |-> "T1" ]
  /\ ret = [ p \in PROC |-> NoVal ]

\* Helper selectors for ends
Empty == mem[LeftHat].next = RightHat

\* Paired-update push on the left end
DoPushLeft(p) ==
  /\ pc[p] = "T1"
  /\ \E n \in free, v \in VALS:
       LET first == mem[LeftHat].next IN
       /\ mem[first].prev = LeftHat   \* both words match precondition (DCAS-like)
       /\ mem[n].live = FALSE
       /\ mem' =
            [ mem EXCEPT
              ![n]        = [prev |-> LeftHat, next |-> first,    val |-> v,     live |-> TRUE],
              ![LeftHat]  = [@ EXCEPT !.next = n],
              ![first]    = [@ EXCEPT !.prev = n] ]
       /\ free'   = free \ {n}
       /\ valBag' = [valBag EXCEPT ![v] = @ + 1]
       /\ ret'    = ret
       /\ pc'     = [pc EXCEPT ![p] = "T1"]

\* Paired-update push on the right end
DoPushRight(p) ==
  /\ pc[p] = "T1"
  /\ \E n \in free, v \in VALS:
       LET last == mem[RightHat].prev IN
       /\ mem[last].next = RightHat   \* both words match precondition (DCAS-like)
       /\ mem[n].live = FALSE
       /\ mem' =
            [ mem EXCEPT
              ![n]         = [prev |-> last,     next |-> RightHat, val |-> v,     live |-> TRUE],
              ![RightHat]  = [@ EXCEPT !.prev = n],
              ![last]      = [@ EXCEPT !.next = n] ]
       /\ free'   = free \ {n}
       /\ valBag' = [valBag EXCEPT ![v] = @ + 1]
       /\ ret'    = ret
       /\ pc'     = [pc EXCEPT ![p] = "T1"]

\* Paired-update pop on the left end
DoPopLeft(p) ==
  /\ pc[p] = "T1"
  /\ IF Empty THEN
       /\ ret' = [ret EXCEPT ![p] = NoVal]
       /\ UNCHANGED << mem, free, valBag >>
     ELSE
       LET first  == mem[LeftHat].next IN
       LET second == mem[first].next IN
       LET v      == mem[first].val IN
       /\ mem[first].prev = LeftHat
       /\ mem[second].prev = first   \* both words match precondition (DCAS-like)
       /\ mem' =
            [ mem EXCEPT
              ![LeftHat] = [@ EXCEPT !.next = second],
              ![second]  = [@ EXCEPT !.prev = LeftHat],
              ![first]   = [@ EXCEPT !.prev = NullAddr, !.next = NullAddr, !.live = FALSE] ]
       /\ free'   = free \cup {first}
       /\ valBag' = [valBag EXCEPT ![v] = @ - 1]
       /\ ret'    = [ret EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "T1"]

\* Paired-update pop on the right end
DoPopRight(p) ==
  /\ pc[p] = "T1"
  /\ IF mem[RightHat].prev = LeftHat THEN
       /\ ret' = [ret EXCEPT ![p] = NoVal]
       /\ UNCHANGED << mem, free, valBag >>
     ELSE
       LET last  == mem[RightHat].prev IN
       LET prev2 == mem[last].prev IN
       LET v     == mem[last].val IN
       /\ mem[last].next = RightHat
       /\ mem[prev2].next = last     \* both words match precondition (DCAS-like)
       /\ mem' =
            [ mem EXCEPT
              ![RightHat] = [@ EXCEPT !.prev = prev2],
              ![prev2]    = [@ EXCEPT !.next = RightHat],
              ![last]     = [@ EXCEPT !.prev = NullAddr, !.next = NullAddr, !.live = FALSE] ]
       /\ free'   = free \cup {last}
       /\ valBag' = [valBag EXCEPT ![v] = @ - 1]
       /\ ret'    = [ret EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "T1"]

Next ==
  \E p \in PROC:
    DoPushLeft(p) \/ DoPushRight(p) \/ DoPopLeft(p) \/ DoPopRight(p)

Spec ==
  Init /\ [][Next]_vars /\ Liveness

\* Liveness: every test process returns to T1 infinitely often
TestProcs == PROC
Liveness == \A p \in TestProcs: []<>(pc[p] = "T1")

\* Safety invariants

TypeOK ==
  /\ mem \in [ADDR -> NodeType]
  /\ free \subseteq (ADDR \ {LeftHat, RightHat})
  /\ valBag \in [VALS -> Nat]
  /\ pc \in [PROC -> {"T1"}]
  /\ ret \in [PROC -> (VALS \cup {NoVal})]

SentinelOK ==
  /\ mem[LeftHat].live = TRUE
  /\ mem[RightHat].live = TRUE
  /\ mem[LeftHat].prev = NullAddr
  /\ mem[RightHat].next = NullAddr
  /\ (Empty \/ mem[mem[LeftHat].next].prev = LeftHat)
  /\ (mem[RightHat].prev = LeftHat \/ mem[mem[RightHat].prev].next = RightHat)

FreeLiveOK ==
  /\ LeftHat \notin free /\ RightHat \notin free
  /\ \A a \in (ADDR \ {LeftHat, RightHat}): (mem[a].live <=> a \notin free)

DoublyLinkedOK ==
  \A a \in ADDR:
    IF LiveData(a) THEN
      /\ mem[a].prev \in ADDR /\ mem[a].next \in ADDR
      /\ mem[mem[a].prev].next = a
      /\ mem[mem[a].next].prev = a
    ELSE TRUE

Inv == TypeOK /\ SentinelOK /\ FreeLiveOK /\ DoublyLinkedOK

=============================================================================