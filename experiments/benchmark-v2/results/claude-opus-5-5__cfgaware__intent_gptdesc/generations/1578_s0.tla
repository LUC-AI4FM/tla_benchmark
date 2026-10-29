---------------------------- MODULE DCASDeque ----------------------------
(***************************************************************************)
(* A lock-free concurrent double-ended queue (Snark-style) built from      *)
(* linked nodes and the DCAS (double compare-and-swap) primitive.          *)
(*                                                                         *)
(*  - Nodes live in a pool of addresses and are allocated from a free set. *)
(*    Allocation can fail, and the push then returns "full".               *)
(*  - A background garbage collector, GC, may reclaim any node that is     *)
(*    unreachable from the hats, the Dummy sentinel and every client's     *)
(*    local pointers.                                                      *)
(*  - Clients perform pushL/pushR/popL/popR forever, with retries.         *)
(*  - An abstract sequential deque `queue` is updated at each              *)
(*    linearization point. `absResult` records the response the            *)
(*    sequential deque would give at that point. Linearizability requires *)
(*    the concrete response to equal the abstract one.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Val, Address, Dummy, Procs, null, GC, defaultInitValue

Addr   == Address \cup {Dummy}
Sides  == {"L", "R"}
Opp(s) == IF s = "L" THEN "R" ELSE "L"

NullNode == [L |-> null, R |-> null, V |-> null]

VARIABLES Mem,        \* Mem[a] = [L |-> .., R |-> .., V |-> ..]
          freeList,   \* addresses available for allocation
          Hat,        \* Hat["L"] = LeftHat, Hat["R"] = RightHat
          queue,      \* abstract sequential deque
          pc,         \* control state of each client
          op, side, val, nd, rh, lh, tmp,   \* client locals
          result,     \* concrete response
          absResult   \* response of the abstract deque at linearization

vars == <<Mem, freeList, Hat, queue, pc, op, side, val, nd, rh, lh, tmp,
          result, absResult>>

LeftHat  == Hat["L"]
RightHat == Hat["R"]

-----------------------------------------------------------------------------
(* Reachability, used by the garbage collector and for memory safety.      *)

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  LET T == (S \cup {Mem[a][f] : a \in S, f \in Sides}) \cap Addr
  IN  IF T = S THEN S ELSE ReachFrom(T)

Roots ==
  ({Hat["L"], Hat["R"], Dummy}
     \cup {nd[p] : p \in Procs} \cup {rh[p] : p \in Procs}
     \cup {lh[p] : p \in Procs} \cup {tmp[p] : p \in Procs}) \cap Addr

Reachable == ReachFrom(Roots)

-----------------------------------------------------------------------------
(* Abstract sequential deque operations.                                   *)

AbsPush(s, v) == IF s = "R" THEN Append(queue, v) ELSE <<v>> \o queue

AbsPopVal(s) ==
  IF queue = <<>> THEN "error"
  ELSE IF s = "R" THEN queue[Len(queue)] ELSE Head(queue)

AbsPopQueue(s) ==
  IF queue = <<>> THEN queue
  ELSE IF s = "R" THEN SubSeq(queue, 1, Len(queue) - 1) ELSE Tail(queue)

Set(f, p, x) == [f EXCEPT ![p] = x]

-----------------------------------------------------------------------------
Init ==
  /\ Mem = [a \in Addr |-> IF a = Dummy THEN [L |-> Dummy, R |-> Dummy, V |-> null]
                                        ELSE NullNode]
  /\ freeList = Address \ {Dummy}
  /\ Hat = [s \in Sides |-> Dummy]
  /\ queue = <<>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ op = [p \in Procs |-> defaultInitValue]
  /\ side = [p \in Procs |-> defaultInitValue]
  /\ val = [p \in Procs |-> defaultInitValue]
  /\ nd = [p \in Procs |-> defaultInitValue]
  /\ rh = [p \in Procs |-> defaultInitValue]
  /\ lh = [p \in Procs |-> defaultInitValue]
  /\ tmp = [p \in Procs |-> defaultInitValue]
  /\ result = [p \in Procs |-> defaultInitValue]
  /\ absResult = [p \in Procs |-> defaultInitValue]

-----------------------------------------------------------------------------
(* Invocation                                                              *)

Invoke(p) ==
  /\ pc[p] = "idle"
  /\ \E o \in {"push", "pop"}, s \in Sides :
       /\ op' = Set(op, p, o)
       /\ side' = Set(side, p, s)
       /\ IF o = "push"
            THEN \E v \in Val : /\ val' = Set(val, p, v)
                                /\ pc' = Set(pc, p, "alloc")
            ELSE /\ val' = val
                 /\ pc' = Set(pc, p, "pp1")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, nd, rh, lh, tmp, result, absResult>>

-----------------------------------------------------------------------------
(* Push                                                                    *)

Alloc(p) ==
  /\ pc[p] = "alloc"
  /\ IF freeList = {}
       THEN /\ result' = Set(result, p, "full")
            /\ absResult' = Set(absResult, p, "full")
            /\ pc' = Set(pc, p, "ret")
            /\ UNCHANGED <<Mem, freeList, nd>>
       ELSE \E a \in freeList :
              /\ freeList' = freeList \ {a}
              /\ nd' = Set(nd, p, a)
              /\ Mem' = [Mem EXCEPT ![a] =
                           [f \in {"L", "R", "V"} |->
                              IF f = side[p] THEN Dummy
                              ELSE IF f = "V" THEN val[p] ELSE null]]
              /\ pc' = Set(pc, p, "rd1")
              /\ UNCHANGED <<result, absResult>>
  /\ UNCHANGED <<Hat, queue, op, side, val, rh, lh, tmp>>

PushRd1(p) ==
  /\ pc[p] = "rd1"
  /\ rh' = Set(rh, p, Hat[side[p]])
  /\ pc' = Set(pc, p, "rd2")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, lh, tmp,
                 result, absResult>>

PushRd2(p) ==
  /\ pc[p] = "rd2"
  /\ tmp' = Set(tmp, p, Mem[rh[p]][side[p]])
  /\ pc' = Set(pc, p, "rd3")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, rh, lh,
                 result, absResult>>

PushRd3(p) ==
  /\ pc[p] = "rd3"
  /\ IF tmp[p] = rh[p]
       THEN /\ Mem' = [Mem EXCEPT ![nd[p]][Opp(side[p])] = Dummy]
            /\ pc' = Set(pc, p, "rd4")
       ELSE /\ Mem' = [Mem EXCEPT ![nd[p]][Opp(side[p])] = rh[p]]
            /\ pc' = Set(pc, p, "casNE")
  /\ UNCHANGED <<freeList, Hat, queue, op, side, val, nd, rh, lh, tmp,
                 result, absResult>>

PushRd4(p) ==
  /\ pc[p] = "rd4"
  /\ lh' = Set(lh, p, Hat[Opp(side[p])])
  /\ pc' = Set(pc, p, "casE")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, rh, tmp,
                 result, absResult>>

\* DCAS on both hats: push onto an empty deque
PushCasE(p) ==
  /\ pc[p] = "casE"
  /\ LET s == side[p] IN
       IF Hat[s] = rh[p] /\ Hat[Opp(s)] = lh[p]
         THEN /\ Hat' = [x \in Sides |-> nd[p]]
              /\ queue' = AbsPush(s, val[p])
              /\ result' = Set(result, p, "okay")
              /\ absResult' = Set(absResult, p, "okay")
              /\ pc' = Set(pc, p, "ret")
         ELSE /\ pc' = Set(pc, p, "rd1")
              /\ UNCHANGED <<Hat, queue, result, absResult>>
  /\ UNCHANGED <<Mem, freeList, op, side, val, nd, rh, lh, tmp>>

\* DCAS on the near hat and the outer link of the hat node
PushCasNE(p) ==
  /\ pc[p] = "casNE"
  /\ LET s == side[p] IN
       IF Hat[s] = rh[p] /\ Mem[rh[p]][s] = tmp[p]
         THEN /\ Hat' = [Hat EXCEPT ![s] = nd[p]]
              /\ Mem' = [Mem EXCEPT ![rh[p]][s] = nd[p]]
              /\ queue' = AbsPush(s, val[p])
              /\ result' = Set(result, p, "okay")
              /\ absResult' = Set(absResult, p, "okay")
              /\ pc' = Set(pc, p, "ret")
         ELSE /\ pc' = Set(pc, p, "rd1")
              /\ UNCHANGED <<Hat, Mem, queue, result, absResult>>
  /\ UNCHANGED <<freeList, op, side, val, nd, rh, lh, tmp>>

-----------------------------------------------------------------------------
(* Pop                                                                     *)

PopRd1(p) ==
  /\ pc[p] = "pp1"
  /\ rh' = Set(rh, p, Hat[side[p]])
  /\ pc' = Set(pc, p, "pp2")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, lh, tmp,
                 result, absResult>>

PopRd2(p) ==
  /\ pc[p] = "pp2"
  /\ lh' = Set(lh, p, Hat[Opp(side[p])])
  /\ pc' = Set(pc, p, "pp3")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, rh, tmp,
                 result, absResult>>

PopRd3(p) ==
  /\ pc[p] = "pp3"
  /\ tmp' = Set(tmp, p, Mem[rh[p]][side[p]])
  /\ IF Mem[rh[p]][side[p]] = rh[p]
       THEN /\ result' = Set(result, p, "empty")
            /\ absResult' = Set(absResult, p,
                              IF queue = <<>> THEN "empty" ELSE "error")
            /\ pc' = Set(pc, p, "ret")
       ELSE /\ pc' = Set(pc, p, IF rh[p] = lh[p] THEN "casOne" ELSE "pp4")
            /\ UNCHANGED <<result, absResult>>
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, rh, lh>>

PopRd4(p) ==
  /\ pc[p] = "pp4"
  /\ tmp' = Set(tmp, p, Mem[rh[p]][Opp(side[p])])
  /\ pc' = Set(pc, p, "casMany")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, rh, lh,
                 result, absResult>>

\* DCAS on both hats: pop the only element
PopCasOne(p) ==
  /\ pc[p] = "casOne"
  /\ LET s == side[p] IN
       IF Hat[s] = rh[p] /\ Hat[Opp(s)] = lh[p]
         THEN /\ Hat' = [x \in Sides |-> Dummy]
              /\ absResult' = Set(absResult, p, AbsPopVal(s))
              /\ queue' = AbsPopQueue(s)
              /\ pc' = Set(pc, p, "readV")
         ELSE /\ pc' = Set(pc, p, "pp1")
              /\ UNCHANGED <<Hat, queue, absResult>>
  /\ UNCHANGED <<Mem, freeList, op, side, val, nd, rh, lh, tmp, result>>

\* DCAS on the near hat and the inner link (self-pointer marks node popped)
PopCasMany(p) ==
  /\ pc[p] = "casMany"
  /\ LET s == side[p] IN
       IF Hat[s] = rh[p] /\ Mem[rh[p]][Opp(s)] = tmp[p]
         THEN /\ Hat' = [Hat EXCEPT ![s] = tmp[p]]
              /\ Mem' = [Mem EXCEPT ![rh[p]][Opp(s)] = rh[p]]
              /\ absResult' = Set(absResult, p, AbsPopVal(s))
              /\ queue' = AbsPopQueue(s)
              /\ pc' = Set(pc, p, "readV")
         ELSE /\ pc' = Set(pc, p, "pp1")
              /\ UNCHANGED <<Hat, Mem, queue, absResult>>
  /\ UNCHANGED <<freeList, op, side, val, nd, rh, lh, tmp, result>>

PopReadV(p) ==
  /\ pc[p] = "readV"
  /\ result' = Set(result, p, Mem[rh[p]].V)
  /\ pc' = Set(pc, p, "ret")
  /\ UNCHANGED <<Mem, freeList, Hat, queue, op, side, val, nd, rh, lh, tmp,
                 absResult>>

-----------------------------------------------------------------------------
(* Response: the operation returns and the client clears its locals        *)

Return(p) ==
  /\ pc[p] = "ret"
  /\ pc' = Set(pc, p, "idle")
  /\ op' = Set(op, p, defaultInitValue)
  /\ side' = Set(side, p, defaultInitValue)
  /\ val' = Set(val, p, defaultInitValue)
  /\ nd' = Set(nd, p, defaultInitValue)
  /\ rh' = Set(rh, p, defaultInitValue)
  /\ lh' = Set(lh, p, defaultInitValue)
  /\ tmp' = Set(tmp, p, defaultInitValue)
  /\ result' = Set(result, p, defaultInitValue)
  /\ absResult' = Set(absResult, p, defaultInitValue)
  /\ UNCHANGED <<Mem, freeList, Hat, queue>>

Client(p) ==
  \/ Invoke(p)
  \/ Alloc(p) \/ PushRd1(p) \/ PushRd2(p) \/ PushRd3(p) \/ PushRd4(p)
  \/ PushCasE(p) \/ PushCasNE(p)
  \/ PopRd1(p) \/ PopRd2(p) \/ PopRd3(p) \/ PopRd4(p)
  \/ PopCasOne(p) \/ PopCasMany(p) \/ PopReadV(p)
  \/ Return(p)

-----------------------------------------------------------------------------
(* Garbage collector, process GC: reclaims one unreachable node.           *)

Collect ==
  \E a \in Address \ (freeList \cup {Dummy} \cup Reachable) :
     /\ freeList' = freeList \cup {a}
     /\ Mem' = [Mem EXCEPT ![a] = NullNode]
     /\ UNCHANGED <<Hat, queue, pc, op, side, val, nd, rh, lh, tmp,
                    result, absResult>>

Next == Collect \/ \E p \in Procs : Client(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(Client(p))

-----------------------------------------------------------------------------
(* Properties                                                              *)

PCs == {"idle", "alloc", "rd1", "rd2", "rd3", "rd4", "casE", "casNE",
        "pp1", "pp2", "pp3", "pp4", "casOne", "casMany", "readV", "ret"}

TypeOK ==
  /\ Mem \in [Addr -> [L : Addr \cup {null}, R : Addr \cup {null},
                       V : Val \cup {null}]]
  /\ freeList \subseteq Address \ {Dummy}
  /\ Hat \in [Sides -> Addr]
  /\ queue \in Seq(Val)
  /\ pc \in [Procs -> PCs]

\* Every completed operation returns what the sequential deque returns at
\* its linearization point.
Linearizable ==
  \A p \in Procs : pc[p] = "ret" =>
     /\ absResult[p] # "error"
     /\ result[p] = absResult[p]

\* No node is reclaimed or reused while it is reachable.
MemorySafety == Reachable \cap freeList = {}

\* The hats are consistent and the Dummy sentinel is intact.
StructuralIntegrity ==
  /\ \A s \in Sides : Hat[s] \notin freeList
  /\ Mem[Dummy].L = Dummy /\ Mem[Dummy].R = Dummy
  /\ (Hat["L"] = Dummy) <=> (Hat["R"] = Dummy)

\* No value is created from nothing: the abstract deque never holds more
\* elements than there are allocated nodes.
NoDuplication == Len(queue) <= Cardinality(Address \ (freeList \cup {Dummy}))

\* The system as a whole keeps making progress.
Progress == \A p \in Procs : (pc[p] # "idle") ~> (\E q \in Procs : pc[q] = "ret")

Symmetry == Permutations(Address \ {Dummy}) \cup Permutations(Procs)

=============================================================================