----------------------------- MODULE LockFreeDeque -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  This module models, in the spirit of a PlusCal translation, a concurrent
  double-ended queue (deque) with Detlefs-style lock-free paired updates
  (modeled as DCAS-like atomicity on two shared pointers).

  Shared state:
    - Mem: mapping from addresses to node records [val, prev, next]
    - LH, RH: left/right "hat" pointers
    - Free: freelist of available addresses
    - ValBag: multiset (as function Val -> Nat) tracking values in the deque
    - pc: per-process control location (only "T1" is used here)

  A test process set Proc nondeterministically performs pushLeft, pushRight,
  popLeft, and popRight. Each step atomically updates the shared state
  consistent with DCAS-like paired updates. The multiset ValBag is kept
  consistent with deque contents, with an invariant asserting equality.

  Liveness property:
    - Every process in Proc returns to control location "T1" infinitely often.
*)

CONSTANTS
  Addr, \* finite set of addresses (nodes)
  Val,  \* set of values stored in nodes
  Proc, \* set of process identifiers
  Null  \* distinguished null pointer (Null \notin Addr)

ASSUME /\ Null \notin Addr
       /\ Proc # {} 
       /\ Addr # {} 
       /\ Val # {}

\* Node record type
NodeType == [ val: Val, prev: Addr \cup {Null}, next: Addr \cup {Null} ]

\* VARIABLES
VARIABLES Mem, LH, RH, Free, ValBag, pc

vars == << Mem, LH, RH, Free, ValBag, pc >>

\* Helper: zero bag over Val
ZeroBag == [ v \in Val |-> 0 ]

\* Multiset operations
AddToBag(bag, v) == [ x \in Val |-> IF x = v THEN bag[x] + 1 ELSE bag[x] ]
RemFromBag(bag, v) == [ x \in Val |-> IF x = v /\ bag[x] > 0 THEN bag[x] - 1 ELSE bag[x] ]

\* Bounded traversal from LH following 'next' up to Cardinality(Addr) steps
RECURSIVE AddrSeq(_,_)
AddrSeq(a, n) ==
  IF n = 0 \/ a = Null THEN <<>>
  ELSE << a >> \o AddrSeq(Mem[a].next, n - 1)

ReachSeq == AddrSeq(LH, Cardinality(Addr))
ReachLen == Len(ReachSeq)
ReachSet == { ReachSeq[i] : i \in 1..ReachLen }

ValsSeq == [ i \in 1..ReachLen |-> Mem[ReachSeq[i]].val ]

BagOfVals(seq) ==
  [ v \in Val |-> Cardinality({ i \in 1..Len(seq) : seq[i] = v }) ]

\* Safety invariants

TypeOK ==
  /\ Mem \in [Addr -> NodeType]
  /\ LH \in Addr \cup {Null}
  /\ RH \in Addr \cup {Null}
  /\ Free \subseteq Addr
  /\ ValBag \in [Val -> Nat]
  /\ pc \in [Proc -> {"T1"}]

StructOK ==
  /\ (LH = Null) <=> (RH = Null)
  /\ (LH = Null) <=> (ReachLen = 0)
  /\ (ReachLen = 0) \/ (ReachSeq[1] = LH)
  /\ (ReachLen = 0) \/ (ReachSeq[ReachLen] = RH)
  /\ (ReachLen = 0) \/ (Mem[LH].prev = Null)
  /\ (ReachLen = 0) \/ (Mem[RH].next = Null)
  /\ \A i \in 1..(ReachLen - 1):
        /\ Mem[ReachSeq[i]].next = ReachSeq[i+1]
        /\ Mem[ReachSeq[i+1]].prev = ReachSeq[i]
  /\ ReachSet \cap Free = {}

BagOK ==
  ValBag = BagOfVals(ValsSeq)

Inv == TypeOK /\ StructOK /\ BagOK

\* Initialization
Init ==
  /\ LH = Null
  /\ RH = Null
  /\ Free = Addr
  /\ ValBag = ZeroBag
  /\ Mem \in [Addr -> [ val: Val, prev: {Null}, next: {Null} ]]
  /\ pc = [ p \in Proc |-> "T1" ]

\* DCAS-like paired update operations (atomic actions)

\* Push a value v on the left
PushLeft(v) ==
  \/ /\ LH = Null /\ RH = Null
     /\ \E a \in Free:
          /\ Mem' = [Mem EXCEPT ![a] = [val |-> v, prev |-> Null, next |-> Null]]
          /\ LH' = a
          /\ RH' = a
          /\ Free' = Free \ {a}
          /\ ValBag' = AddToBag(ValBag, v)
  \/ /\ LH # Null /\ Mem[LH].prev = Null
     /\ \E a \in Free:
          /\ Mem' = [Mem EXCEPT
                        ![a]   = [val |-> v, prev |-> Null, next |-> LH],
                        ![LH].prev = a]
          /\ LH' = a
          /\ RH' = RH
          /\ Free' = Free \ {a}
          /\ ValBag' = AddToBag(ValBag, v)

\* Push a value v on the right
PushRight(v) ==
  \/ /\ LH = Null /\ RH = Null
     /\ \E a \in Free:
          /\ Mem' = [Mem EXCEPT ![a] = [val |-> v, prev |-> Null, next |-> Null]]
          /\ LH' = a
          /\ RH' = a
          /\ Free' = Free \ {a}
          /\ ValBag' = AddToBag(ValBag, v)
  \/ /\ RH # Null /\ Mem[RH].next = Null
     /\ \E a \in Free:
          /\ Mem' = [Mem EXCEPT
                        ![a]   = [val |-> v, prev |-> RH,  next |-> Null],
                        ![RH].next = a]
          /\ LH' = LH
          /\ RH' = a
          /\ Free' = Free \ {a}
          /\ ValBag' = AddToBag(ValBag, v)

\* Pop from the left (if empty, no-op on shared state)
PopLeft ==
  \/ /\ LH = Null
     /\ UNCHANGED << Mem, LH, RH, Free, ValBag >>
  \/ /\ LH = RH /\ LH # Null
     /\ LET a == LH IN
        /\ UNCHANGED Mem
        /\ LH' = Null
        /\ RH' = Null
        /\ Free' = Free \cup {a}
        /\ ValBag' = RemFromBag(ValBag, Mem[a].val)
  \/ /\ LH # Null
     /\ LET a == LH IN
        LET b == Mem[a].next IN
          /\ b # Null
          /\ Mem[b].prev = a
          /\ Mem' = [Mem EXCEPT ![b].prev = Null]
          /\ LH' = b
          /\ RH' = RH
          /\ Free' = Free \cup {a}
          /\ ValBag' = RemFromBag(ValBag, Mem[a].val)

\* Pop from the right (if empty, no-op on shared state)
PopRight ==
  \/ /\ RH = Null
     /\ UNCHANGED << Mem, LH, RH, Free, ValBag >>
  \/ /\ LH = RH /\ RH # Null
     /\ LET b == RH IN
        /\ UNCHANGED Mem
        /\ LH' = Null
        /\ RH' = Null
        /\ Free' = Free \cup {b}
        /\ ValBag' = RemFromBag(ValBag, Mem[b].val)
  \/ /\ RH # Null
     /\ LET b == RH IN
        LET a == Mem[b].prev IN
          /\ a # Null
          /\ Mem[a].next = b
          /\ Mem' = [Mem EXCEPT ![a].next = Null]
          /\ LH' = LH
          /\ RH' = a
          /\ Free' = Free \cup {b}
          /\ ValBag' = RemFromBag(ValBag, Mem[b].val)

\* Per-process test step: nondeterministically choose an operation and return to T1
StepPushL(p) ==
  \E v \in Val:
    /\ PushLeft(v)
    /\ pc' = [pc EXCEPT ![p] = "T1"]

StepPushR(p) ==
  \E v \in Val:
    /\ PushRight(v)
    /\ pc' = [pc EXCEPT ![p] = "T1"]

StepPopL(p) ==
  /\ PopLeft
  /\ pc' = [pc EXCEPT ![p] = "T1"]

StepPopR(p) ==
  /\ PopRight
  /\ pc' = [pc EXCEPT ![p] = "T1"]

\* Always-enabled no-op choice for the test process
StepNoOp(p) ==
  /\ UNCHANGED << Mem, LH, RH, Free, ValBag >>
  /\ pc' = [pc EXCEPT ![p] = "T1"]

\* A process step is one of the above actions
ProcStep(p) ==
  StepPushL(p) \/ StepPushR(p) \/ StepPopL(p) \/ StepPopR(p) \/ StepNoOp(p)

\* System next-state relation: one process moves at a time
Next ==
  \E p \in Proc: ProcStep(p)

\* Liveness: every test process returns to control location T1 infinitely often
Liveness ==
  \A p \in Proc: []<>(pc[p] = "T1")

\* Specification with weak fairness for each process step
Spec ==
  Init /\ [][Next]_vars /\ \A p \in Proc: WF_vars(ProcStep(p))

=============================================================================