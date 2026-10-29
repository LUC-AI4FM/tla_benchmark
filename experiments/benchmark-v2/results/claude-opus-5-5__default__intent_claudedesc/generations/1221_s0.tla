------------------------------ MODULE LazyCacheStateCount ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,        \* set of processors
          Adr,         \* set of addresses
          Data,        \* set of data values
          NoData,      \* "not present" sentinel for cache entries
          Tag,         \* tag value used for tagged operations
          MaxInQLen,   \* bound on input queue length
          MaxOutQLen   \* bound on output queue length

ASSUME /\ NoData \notin Data
       /\ MaxInQLen \in Nat
       /\ MaxOutQLen \in Nat
       /\ IsFiniteSet(Proc) /\ IsFiniteSet(Adr) /\ IsFiniteSet(Data)

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

-----------------------------------------------------------------------------------------
(* Operations: address-data pairs, optionally tagged *)
UntaggedOp == Adr \X Data
TaggedOp   == Adr \X Data \X {Tag}
Op         == UntaggedOp \cup TaggedOp

(* Responses in the output queue: data-address pairs *)
Resp == Data \X Adr

(* Bounded sequences over S of length at most n *)
BSeq(S, n) == UNION { [1..i -> S] : i \in 0..n }

-----------------------------------------------------------------------------------------
(* Analytical state count *)
SeqCount(n, k) ==
  LET f[i \in 0..k] == IF i = 0 THEN 1 ELSE n^i + f[i-1]
  IN  f[k]

NumData == Cardinality(Data)
NumAdr  == Cardinality(Adr)
NumProc == Cardinality(Proc)
NumOp   == 2 * NumAdr * NumData
NumResp == NumData * NumAdr

MemStates   == NumData ^ NumAdr
CacheStates == (NumData + 1) ^ NumAdr
InQStates   == SeqCount(NumOp, MaxInQLen)
OutQStates  == SeqCount(NumResp, MaxOutQLen)

TotalStates == MemStates * ((CacheStates * InQStates * OutQStates) ^ NumProc)

ASSUME PrintT(<<"Expected number of distinct states:", TotalStates>>)

-----------------------------------------------------------------------------------------
TypeInvariant ==
  /\ mem   \in [Adr -> Data]
  /\ cache \in [Proc -> [Adr -> Data \cup {NoData}]]
  /\ inq   \in [Proc -> BSeq(Op, MaxInQLen)]
  /\ outq  \in [Proc -> BSeq(Resp, MaxOutQLen)]

Init ==
  /\ mem   \in [Adr -> Data]
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoData]]
  /\ inq   = [p \in Proc |-> << >>]
  /\ outq  = [p \in Proc |-> << >>]

UpdateMem ==
  /\ mem' \in [Adr -> Data]
  /\ UNCHANGED <<cache, inq, outq>>

UpdateCache(p) ==
  /\ \E a \in Adr, v \in Data \cup {NoData} :
        cache' = [cache EXCEPT ![p][a] = v]
  /\ UNCHANGED <<mem, inq, outq>>

EnqIn(p) ==
  /\ Len(inq[p]) < MaxInQLen
  /\ \E op \in Op : inq' = [inq EXCEPT ![p] = Append(@, op)]
  /\ UNCHANGED <<mem, cache, outq>>

DeqIn(p) ==
  /\ Len(inq[p]) > 0
  /\ inq' = [inq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, outq>>

EnqOut(p) ==
  /\ Len(outq[p]) < MaxOutQLen
  /\ \E r \in Resp : outq' = [outq EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED <<mem, cache, inq>>

DeqOut(p) ==
  /\ Len(outq[p]) > 0
  /\ outq' = [outq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, inq>>

Next ==
  \/ UpdateMem
  \/ \E p \in Proc :
        \/ UpdateCache(p)
        \/ EnqIn(p)
        \/ DeqIn(p)
        \/ EnqOut(p)
        \/ DeqOut(p)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=========================================================================================