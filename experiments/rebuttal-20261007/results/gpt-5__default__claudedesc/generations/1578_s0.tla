----------------------------- MODULE Snark -----------------------------
EXTENDS Naturals, TLC

CONSTANTS 
  Address,    \* Set of all addresses (heap nodes)
  Procs,      \* Set of processes
  Val,        \* Set of values to push
  Dummy,      \* Distinguished sentinel address in Address
  EMPTY,      \* Distinct return value for empty pops (not in Val)
  NullVal     \* Distinct value used for uninitialized nodes (not in Val)

ASSUME Dummy \in Address /\ EMPTY \notin Val /\ NullVal \notin Val

(*
 State:
  - Mem[a] = [l |-> Address, r |-> Address, v |-> Val \cup {NullVal}]
  - freeList: pool of free addresses available for allocation
  - LeftHat, RightHat: head pointers anchored at Dummy
  - rVal[p]: last return value for process p (either in Val or EMPTY)
  - valBag: multiset of logical values present in the deque (for checking)
  - pc[p]: single control label "T1" marking the loop head
*)
VARIABLES 
  Mem, 
  freeList,
  LeftHat, RightHat,
  rVal,
  valBag,
  pc

vars == << Mem, freeList, LeftHat, RightHat, rVal, valBag, pc >>

\* Bag helpers over Val -> Nat
EmptyBag == [v \in Val |-> 0]
AddToBag(b, v) == [b EXCEPT ![v] = @ + 1]
RemoveFromBag(b, v) == [b EXCEPT ![v] = @ - 1]
InBag(b, v) == b[v] > 0

\* Symmetry sets for model checking
SymmAddrs == Address \ {Dummy}
SymmProcs == Procs

Init ==
  /\ Mem \in [Address -> [l : Address, r : Address, v : Val \cup {NullVal}]]
  /\ Mem = [a \in Address |-> IF a = Dummy 
                               THEN [l |-> Dummy, r |-> Dummy, v |-> NullVal]
                               ELSE [l |-> a,     r |-> a,     v |-> NullVal]]
  /\ freeList = Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal \in [Procs -> (Val \cup {EMPTY})]
  /\ rVal = [p \in Procs |-> EMPTY]
  /\ valBag \in [Val -> Nat]
  /\ valBag = EmptyBag
  /\ pc \in [Procs -> {"T1"}]
  /\ pc = [p \in Procs |-> "T1"]

\* Push a value v to the right end
PushRight(p) ==
  /\ pc[p] = "T1"
  /\ \E v \in Val, a \in freeList:
       \* Two cases: empty deque or non-empty
       (\/ /\ LeftHat = Dummy /\ RightHat = Dummy
           /\ Mem[Dummy].l = Dummy /\ Mem[Dummy].r = Dummy
           /\ LET newMem == 
                 [Mem EXCEPT
                   ![a].l = Dummy,
                   ![a].r = Dummy,
                   ![a].v = v,
                   ![Dummy].l = a,
                   ![Dummy].r = a]
              IN /\ Mem' = newMem
                 /\ LeftHat' = newMem[Dummy].l
                 /\ RightHat' = newMem[Dummy].r
           /\ freeList' = freeList \ {a}
           /\ valBag' = AddToBag(valBag, v)
           /\ UNCHANGED rVal
           /\ pc' = pc
          )
       \/ (/\ RightHat # Dummy
           /\ LET rr == RightHat IN Mem[Dummy].r = rr /\ Mem[rr].r = Dummy
           /\ LET rr == RightHat IN
              LET newMem ==
                [Mem EXCEPT
                   ![a].l = rr,
                   ![a].r = Dummy,
                   ![a].v = v,
                   ![rr].r = a,
                   ![Dummy].r = a]
              IN /\ Mem' = newMem
                 /\ LeftHat' = newMem[Dummy].l
                 /\ RightHat' = newMem[Dummy].r
           /\ freeList' = freeList \ {a}
           /\ valBag' = AddToBag(valBag, v)
           /\ UNCHANGED rVal
           /\ pc' = pc
          )
  /\ UNCHANGED << >>

\* Push a value v to the left end
PushLeft(p) ==
  /\ pc[p] = "T1"
  /\ \E v \in Val, a \in freeList:
       (\/ /\ LeftHat = Dummy /\ RightHat = Dummy
           /\ Mem[Dummy].l = Dummy /\ Mem[Dummy].r = Dummy
           /\ LET newMem == 
                 [Mem EXCEPT
                   ![a].l = Dummy,
                   ![a].r = Dummy,
                   ![a].v = v,
                   ![Dummy].l = a,
                   ![Dummy].r = a]
              IN /\ Mem' = newMem
                 /\ LeftHat' = newMem[Dummy].l
                 /\ RightHat' = newMem[Dummy].r
           /\ freeList' = freeList \ {a}
           /\ valBag' = AddToBag(valBag, v)
           /\ UNCHANGED rVal
           /\ pc' = pc
          )
       \/ (/\ LeftHat # Dummy
           /\ LET ll == LeftHat IN Mem[Dummy].l = ll /\ Mem[ll].l = Dummy
           /\ LET ll == LeftHat IN
              LET newMem ==
                [Mem EXCEPT
                   ![a].l = Dummy,
                   ![a].r = ll,
                   ![a].v = v,
                   ![ll].l = a,
                   ![Dummy].l = a]
              IN /\ Mem' = newMem
                 /\ LeftHat' = newMem[Dummy].l
                 /\ RightHat' = newMem[Dummy].r
           /\ freeList' = freeList \ {a}
           /\ valBag' = AddToBag(valBag, v)
           /\ UNCHANGED rVal
           /\ pc' = pc
          )
  /\ UNCHANGED << >>

\* Pop a value from the right end
PopRight(p) ==
  /\ pc[p] = "T1"
  /\ (\/ /\ RightHat = Dummy
       /\ rVal' = [rVal EXCEPT ![p] = EMPTY]
       /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, pc >>
      \/ /\ RightHat # Dummy
         /\ LET rr == RightHat IN
            LET prev == Mem[rr].l IN
              (\/ /\ prev = Dummy
                  /\ Mem[Dummy].r = rr /\ Mem[Dummy].l = rr
                  /\ LET rrVal == Mem[rr].v IN
                     /\ Assert(valBag[rrVal] > 0, "popRight: underflow of valBag")
                     /\ LET newMem ==
                           [Mem EXCEPT
                              ![Dummy].r = Dummy,
                              ![Dummy].l = Dummy,
                              ![rr].v = NullVal]
                        IN /\ Mem' = newMem
                           /\ LeftHat' = newMem[Dummy].l
                           /\ RightHat' = newMem[Dummy].r
                     /\ freeList' = freeList \cup {rr}
                     /\ valBag' = RemoveFromBag(valBag, rrVal)
                     /\ rVal' = [rVal EXCEPT ![p] = rrVal]
                     /\ pc' = pc
                 )
              \/ (/\ prev # Dummy
                  /\ Mem[Dummy].r = rr /\ Mem[prev].r = rr
                  /\ LET rrVal == Mem[rr].v IN
                     /\ Assert(valBag[rrVal] > 0, "popRight: underflow of valBag")
                     /\ LET newMem ==
                           [Mem EXCEPT
                              ![Dummy].r = prev,
                              ![prev].r = Dummy,
                              ![rr].v = NullVal]
                        IN /\ Mem' = newMem
                           /\ LeftHat' = newMem[Dummy].l
                           /\ RightHat' = newMem[Dummy].r
                     /\ freeList' = freeList \cup {rr}
                     /\ valBag' = RemoveFromBag(valBag, rrVal)
                     /\ rVal' = [rVal EXCEPT ![p] = rrVal]
                     /\ pc' = pc
                 )
        )
      
\* Pop a value from the left end
PopLeft(p) ==
  /\ pc[p] = "T1"
  /\ (\/ /\ LeftHat = Dummy
       /\ rVal' = [rVal EXCEPT ![p] = EMPTY]
       /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, pc >>
      \/ /\ LeftHat # Dummy
         /\ LET ll == LeftHat IN
            LET next == Mem[ll].r IN
              (\/ /\ next = Dummy
                  /\ Mem[Dummy].l = ll /\ Mem[Dummy].r = ll
                  /\ LET llVal == Mem[ll].v IN
                     /\ Assert(valBag[llVal] > 0, "popLeft: underflow of valBag")
                     /\ LET newMem ==
                           [Mem EXCEPT
                              ![Dummy].l = Dummy,
                              ![Dummy].r = Dummy,
                              ![ll].v = NullVal]
                        IN /\ Mem' = newMem
                           /\ LeftHat' = newMem[Dummy].l
                           /\ RightHat' = newMem[Dummy].r
                     /\ freeList' = freeList \cup {ll}
                     /\ valBag' = RemoveFromBag(valBag, llVal)
                     /\ rVal' = [rVal EXCEPT ![p] = llVal]
                     /\ pc' = pc
                 )
              \/ (/\ next # Dummy
                  /\ Mem[Dummy].l = ll /\ Mem[next].l = ll
                  /\ LET llVal == Mem[ll].v IN
                     /\ Assert(valBag[llVal] > 0, "popLeft: underflow of valBag")
                     /\ LET newMem ==
                           [Mem EXCEPT
                              ![Dummy].l = next,
                              ![next].l = Dummy,
                              ![ll].v = NullVal]
                        IN /\ Mem' = newMem
                           /\ LeftHat' = newMem[Dummy].l
                           /\ RightHat' = newMem[Dummy].r
                     /\ freeList' = freeList \cup {ll}
                     /\ valBag' = RemoveFromBag(valBag, llVal)
                     /\ rVal' = [rVal EXCEPT ![p] = llVal]
                     /\ pc' = pc
                 )
        )

\* One process performs one operation per step
Step(p) == PushRight(p) \/ PushLeft(p) \/ PopRight(p) \/ PopLeft(p)

Next == \E p \in Procs: Step(p)

Spec == Init /\ [][Next]_vars

\* Safety invariants
TypeOK ==
  /\ Mem \in [Address -> [l : Address, r : Address, v : Val \cup {NullVal}]]
  /\ freeList \subseteq Address \ {Dummy}
  /\ LeftHat \in Address /\ RightHat \in Address
  /\ rVal \in [Procs -> (Val \cup {EMPTY})]
  /\ valBag \in [Val -> Nat]
  /\ pc \in [Procs -> {"T1"}]

HeadAnchored ==
  /\ LeftHat = Mem[Dummy].l
  /\ RightHat = Mem[Dummy].r

EndPtrOK ==
  /\ (LeftHat = Dummy) <=> (RightHat = Dummy)
  /\ (RightHat # Dummy => Mem[RightHat].r = Dummy)
  /\ (LeftHat  # Dummy => Mem[LeftHat].l  = Dummy)

\* Liveness (typically disabled in the model config)
Liveness == \A p \in Procs: []<>(pc[p] = "T1")
=======================================================================