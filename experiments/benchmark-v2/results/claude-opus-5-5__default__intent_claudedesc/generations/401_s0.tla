------------------------------ MODULE LazyCacheFingerprint ------------------------------
(***************************************************************************)
(* Fingerprint test for a lazy cache system.                               *)
(*                                                                         *)
(* Shared memory maps addresses to data values. Each processor has a       *)
(* cache that maps each address to a data value or the NoData marker.      *)
(* Each processor also has a bounded input queue of read/write operations  *)
(* and a bounded output queue of address-data pairs.                       *)
(*                                                                         *)
(* Init enumerates every type-correct state, and Next contains the         *)
(* cache-system transitions, all of which preserve the type invariant.     *)
(* So the number of distinct states TLC finds must equal the analytically  *)
(* computed count printed when the model starts.                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,       \* set of processors
          Adr,        \* set of addresses
          Val,        \* set of data values
          NoData,     \* "not dirty"/no-data cache marker
          MaxInLen,   \* maximum length of an input queue
          MaxOutLen   \* maximum length of an output queue

ASSUME /\ NoData \notin Val
       /\ MaxInLen \in Nat
       /\ MaxOutLen \in Nat
       /\ IsFiniteSet(Proc) /\ IsFiniteSet(Adr) /\ IsFiniteSet(Val)

VARIABLES memory, cache, inq, outq

vars == <<memory, cache, inq, outq>>

(***************************************************************************)
(* Operation and queue types                                               *)
(***************************************************************************)
ReadOps  == [op : {"Rd"}, adr : Adr]
WriteOps == [op : {"Wr"}, adr : Adr, val : Val]
Ops      == ReadOps \cup WriteOps

OutEntries == [adr : Adr, val : Val]

\* Sequences over S with length at most n
BSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

TypeOK ==
  /\ memory \in [Adr -> Val]
  /\ cache  \in [Proc -> [Adr -> Val \cup {NoData}]]
  /\ inq    \in [Proc -> BSeq(Ops, MaxInLen)]
  /\ \A p \in Proc : Len(inq[p]) <= MaxInLen
  /\ outq   \in [Proc -> BSeq(OutEntries, MaxOutLen)]
  /\ \A p \in Proc : Len(outq[p]) <= MaxOutLen

(***************************************************************************)
(* Analytical state count                                                  *)
(***************************************************************************)
\* 1 + b + b^2 + ... + b^n  (number of sequences of length <= n over b symbols)
GeomSum(b, n) ==
  LET f[k \in 0..n] == IF k = 0 THEN 1 ELSE b^k + f[k-1]
  IN  f[n]

NumAdr  == Cardinality(Adr)
NumVal  == Cardinality(Val)
NumProc == Cardinality(Proc)
NumOps  == NumAdr + NumAdr * NumVal          \* reads + writes
NumOut  == NumAdr * NumVal

MemStates   == NumVal ^ NumAdr
CacheStates == (NumVal + 1) ^ NumAdr
InqStates   == GeomSum(NumOps, MaxInLen)
OutqStates  == GeomSum(NumOut, MaxOutLen)

ExpectedStates == MemStates * ((CacheStates * InqStates * OutqStates) ^ NumProc)

ASSUME PrintT(<<"Expected number of distinct states:", ExpectedStates>>)

(***************************************************************************)
(* Initial states: every type-correct state                                *)
(***************************************************************************)
Init ==
  /\ memory \in [Adr -> Val]
  /\ cache  \in [Proc -> [Adr -> Val \cup {NoData}]]
  /\ inq    \in [Proc -> BSeq(Ops, MaxInLen)]
  /\ outq   \in [Proc -> BSeq(OutEntries, MaxOutLen)]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
\* Environment issues a read or write request to processor p
Issue(p, o) ==
  /\ Len(inq[p]) < MaxInLen
  /\ inq' = [inq EXCEPT ![p] = Append(@, o)]
  /\ UNCHANGED <<memory, cache, outq>>

\* Lazily fill a cache line from memory
Fill(p, a) ==
  /\ cache[p][a] = NoData
  /\ cache' = [cache EXCEPT ![p][a] = memory[a]]
  /\ UNCHANGED <<memory, inq, outq>>

\* Evict a cache line
Evict(p, a) ==
  /\ cache[p][a] # NoData
  /\ cache' = [cache EXCEPT ![p][a] = NoData]
  /\ UNCHANGED <<memory, inq, outq>>

\* Serve a read at the head of the input queue from the cache
DoRead(p) ==
  /\ inq[p] # << >>
  /\ LET o == Head(inq[p]) IN
       /\ o.op = "Rd"
       /\ cache[p][o.adr] # NoData
       /\ Len(outq[p]) < MaxOutLen
       /\ outq' = [outq EXCEPT ![p] = Append(@, [adr |-> o.adr,
                                                  val |-> cache[p][o.adr]])]
       /\ inq'  = [inq EXCEPT ![p] = Tail(@)]
       /\ UNCHANGED <<memory, cache>>

\* Perform a write at the head of the input queue (write-through to memory)
DoWrite(p) ==
  /\ inq[p] # << >>
  /\ LET o == Head(inq[p]) IN
       /\ o.op = "Wr"
       /\ memory' = [memory EXCEPT ![o.adr] = o.val]
       /\ cache'  = [cache EXCEPT ![p][o.adr] = o.val]
       /\ inq'    = [inq EXCEPT ![p] = Tail(@)]
       /\ UNCHANGED outq

\* Environment consumes a response
Respond(p) ==
  /\ outq[p] # << >>
  /\ outq' = [outq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<memory, cache, inq>>

Next ==
  \/ \E p \in Proc, o \in Ops : Issue(p, o)
  \/ \E p \in Proc, a \in Adr : Fill(p, a) \/ Evict(p, a)
  \/ \E p \in Proc : DoRead(p) \/ DoWrite(p) \/ Respond(p)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
==========================================================================================