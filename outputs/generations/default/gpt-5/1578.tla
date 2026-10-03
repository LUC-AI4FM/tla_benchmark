------------------------------- MODULE DequeDCAS -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Addr,      \* finite set of node addresses
    Val,       \* set of storable values
    P,         \* set of test processes
    Nil        \* distinguished null pointer

ASSUME Nil \notin Addr

(*
State:
  Mem      : memory mapping addresses to node records
  Free     : set of free addresses available for allocation
  LeftHat  : pointer to left end node (Nil if empty)
  RightHat : pointer to right end node (Nil if empty)
  pc       : per-process control location (kept at "T1" for test loop head)
  valBag   : multiset (bag) of values logically in the deque
  lastRet  : last value returned by a pop for each process (or Nil)
*)

VARIABLES Mem, Free, LeftHat, RightHat, pc, valBag, lastRet

NodeRec == [ val : Val, left : Addr \cup {Nil}, right : Addr \cup {Nil} ]

EmptyBag == [ v \in Val |-> 0 ]

AddBag(b, v) == [ b EXCEPT ![v] = b[v] + 1 ]

RemoveBag(b, v) == [ b EXCEPT ![v] = IF b[v] > 0 THEN b[v] - 1 ELSE 0 ]

IsEmpty == (LeftHat = Nil) /\ (RightHat = Nil)

IsSingle == (LeftHat # Nil) /\ (LeftHat = RightHat)

RECURSIVE RightN(_, _)
RightN(a, n) ==
  IF n = 0 THEN a
  ELSE IF a = Nil THEN Nil
       ELSE RightN(Mem[a].right, n - 1)

InDeque(a) ==
  \E n \in 0..Cardinality(Addr) : RightN(LeftHat, n) = a

DequeSet == { a \in Addr : InDeque(a) }

ValBagFromStruct ==
  [ v \in Val |-> Cardinality({ a \in DequeSet : Mem[a].val = v }) ]

TypeOK ==
  /\ Mem \in [Addr -> NodeRec]
  /\ Free \subseteq Addr
  /\ LeftHat \in Addr \cup {Nil}
  /\ RightHat \in Addr \cup {Nil}
  /\ pc \in [P -> {"T1"}]
  /\ valBag \in [Val -> Nat]
  /\ lastRet \in [P -> (Val \cup {Nil})]

InvEndsNil == (LeftHat = Nil) <=> (RightHat = Nil)

InvHeadLeftNil == (LeftHat = Nil) \/ (Mem[LeftHat].left = Nil)

InvTailRightNil == (RightHat = Nil) \/ (Mem[RightHat].right = Nil)

InvBiLinks ==
  \A a \in DequeSet :
    LET r == Mem[a].right IN (r = Nil) \/ (Mem[r].left = a)

InvNoFreeInDeque == (DequeSet \cap Free) = {}

InvBagOK == valBag = ValBagFromStruct

Invariant == TypeOK /\ InvEndsNil /\ InvHeadLeftNil /\ InvTailRightNil /\ InvBiLinks /\ InvNoFreeInDeque /\ InvBagOK

Init ==
  /\ Mem \in [Addr -> NodeRec]
  /\ \A a \in Addr : (Mem[a].left = Nil) /\ (Mem[a].right = Nil)
  /\ Free = Addr
  /\ LeftHat = Nil
  /\ RightHat = Nil
  /\ pc = [p \in P |-> "T1"]
  /\ valBag = EmptyBag
  /\ lastRet \in [p \in P |-> Val \cup {Nil}]

PushLeftAct(p) ==
  /\ pc[p] = "T1"
  /\ \E x \in Free, v \in Val :
        /\ IF IsEmpty THEN
              /\ Mem' = [Mem EXCEPT ![x] = [ val |-> v, left |-> Nil, right |-> Nil ]]
              /\ LeftHat' = x
              /\ RightHat' = x
           ELSE
              /\ LET old == LeftHat IN
                   /\ old \in Addr
                   /\ Mem[old].left = Nil \* DCAS-like expect on old.left
                   /\ Mem' = [Mem EXCEPT
                               ![x]    = [ val |-> v, left |-> Nil, right |-> old ],
                               ![old].left = x]
                   /\ LeftHat' = x
                   /\ RightHat' = RightHat
        /\ Free' = Free \ {x}
        /\ valBag' = AddBag(valBag, v)
        /\ lastRet' = [lastRet EXCEPT ![p] = Nil]
        /\ pc' = pc

PushRightAct(p) ==
  /\ pc[p] = "T1"
  /\ \E x \in Free, v \in Val :
        /\ IF IsEmpty THEN
              /\ Mem' = [Mem EXCEPT ![x] = [ val |-> v, left |-> Nil, right |-> Nil ]]
              /\ LeftHat' = x
              /\ RightHat' = x
           ELSE
              /\ LET old == RightHat IN
                   /\ old \in Addr
                   /\ Mem[old].right = Nil \* DCAS-like expect on old.right
                   /\ Mem' = [Mem EXCEPT
                               ![x]     = [ val |-> v, left |-> old, right |-> Nil ],
                               ![old].right = x]
                   /\ RightHat' = x
                   /\ LeftHat' = LeftHat
        /\ Free' = Free \ {x}
        /\ valBag' = AddBag(valBag, v)
        /\ lastRet' = [lastRet EXCEPT ![p] = Nil]
        /\ pc' = pc

PopLeftEmptyAct(p) ==
  /\ pc[p] = "T1"
  /\ IsEmpty
  /\ UNCHANGED << Mem, Free, LeftHat, RightHat, valBag >>
  /\ lastRet' = [lastRet EXCEPT ![p] = Nil]
  /\ pc' = pc

PopLeftSingleAct(p) ==
  /\ pc[p] = "T1"
  /\ IsSingle
  /\ LET a == LeftHat IN
       /\ valBag' = RemoveBag(valBag, Mem[a].val)
       /\ Free' = Free \cup {a}
       /\ Mem' = [Mem EXCEPT ![a] = [ val |-> Mem[a].val, left |-> Nil, right |-> Nil ]]
       /\ LeftHat' = Nil
       /\ RightHat' = Nil
       /\ lastRet' = [lastRet EXCEPT ![p] = Mem[a].val]
       /\ pc' = pc

PopLeftMultiAct(p) ==
  /\ pc[p] = "T1"
  /\ ~IsEmpty /\ ~IsSingle
  /\ LET a == LeftHat IN
     LET b == Mem[a].right IN
       /\ b \in Addr
       /\ Mem[b].left = a \* DCAS-like paired expectation
       /\ valBag' = RemoveBag(valBag, Mem[a].val)
       /\ Free' = Free \cup {a}
       /\ Mem' = [Mem EXCEPT ![a].right = Nil, ![b].left = Nil]
       /\ LeftHat' = b
       /\ RightHat' = RightHat
       /\ lastRet' = [lastRet EXCEPT ![p] = Mem[a].val]
       /\ pc' = pc

PopRightEmptyAct(p) ==
  /\ pc[p] = "T1"
  /\ IsEmpty
  /\ UNCHANGED << Mem, Free, LeftHat, RightHat, valBag >>
  /\ lastRet' = [lastRet EXCEPT ![p] = Nil]
  /\ pc' = pc

PopRightSingleAct(p) ==
  /\ pc[p] = "T1"
  /\ IsSingle
  /\ LET a == RightHat IN
       /\ valBag' = RemoveBag(valBag, Mem[a].val)
       /\ Free' = Free \cup {a}
       /\ Mem' = [Mem EXCEPT ![a] = [ val |-> Mem[a].val, left |-> Nil, right |-> Nil ]]
       /\ LeftHat' = Nil
       /\ RightHat' = Nil
       /\ lastRet' = [lastRet EXCEPT ![p] = Mem[a].val]
       /\ pc' = pc

PopRightMultiAct(p) ==
  /\ pc[p] = "T1"
  /\ ~IsEmpty /\ ~IsSingle
  /\ LET a == RightHat IN
     LET b == Mem[a].left IN
       /\ b \in Addr
       /\ Mem[b].right = a \* DCAS-like paired expectation
       /\ valBag' = RemoveBag(valBag, Mem[a].val)
       /\ Free' = Free \cup {a}
       /\ Mem' = [Mem EXCEPT ![a].left = Nil, ![b].right = Nil]
       /\ RightHat' = b
       /\ LeftHat' = LeftHat
       /\ lastRet' = [lastRet EXCEPT ![p] = Mem[a].val]
       /\ pc' = pc

ProcStep(p) ==
  PushLeftAct(p)
  \/ PushRightAct(p)
  \/ PopLeftEmptyAct(p)
  \/ PopLeftSingleAct(p)
  \/ PopLeftMultiAct(p)
  \/ PopRightEmptyAct(p)
  \/ PopRightSingleAct(p)
  \/ PopRightMultiAct(p)

Next ==
  \E p \in P : ProcStep(p)

vars == << Mem, Free, LeftHat, RightHat, pc, valBag, lastRet >>

Spec ==
  Init /\ [][Next]_vars /\ \A p \in P : WF_vars(ProcStep(p))

TestLiveness == \A p \in P : []<>(pc[p] = "T1")

=============================================================================