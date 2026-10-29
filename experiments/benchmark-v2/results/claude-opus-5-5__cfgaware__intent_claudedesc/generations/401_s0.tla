------------------------------ MODULE LazyCacheFingerprint ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Data,      \* set of data values
          InitData,  \* initial value of every memory location
          Addr,      \* set of addresses
          N,         \* number of processors
          InLen,     \* maximum length of an input queue
          OutLen,    \* maximum length of an output queue
          ND         \* the "not dirty" / no-data marker held in a cache

ASSUME /\ InitData \in Data
       /\ ND \notin Data
       /\ N \in Nat
       /\ InLen \in Nat
       /\ OutLen \in Nat

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

Proc == 1..N

\* Input operations: reads carry an address, writes carry an address,
\* a data value, and the "W" marker that distinguishes them from reads.
RdOps == [op : {"R"}, adr : Addr]
WrOps == [op : {"W"}, adr : Addr, val : Data]
Ops   == RdOps \cup WrOps

\* Output entries are address-data pairs.
OutEntries == Addr \X Data

-----------------------------------------------------------------------------------------
(* Analytic count of the state space.                                                  *)

RECURSIVE GeoSum(_, _)
GeoSum(m, n) == IF n = 0 THEN 1 ELSE m^n + GeoSum(m, n - 1)

MemCount   == Cardinality(Data) ^ Cardinality(Addr)
CacheCount == (Cardinality(Data) + 1) ^ Cardinality(Addr)
InCount    == GeoSum(Cardinality(Ops), InLen)
OutCount   == GeoSum(Cardinality(OutEntries), OutLen)

TotalStates == MemCount * ((CacheCount * InCount * OutCount) ^ N)

-----------------------------------------------------------------------------------------

Init ==
  /\ PrintT(<<"Expected number of distinct states:", TotalStates>>)
  /\ mem   = [a \in Addr |-> InitData]
  /\ cache = [p \in Proc |-> [a \in Addr |-> ND]]
  /\ inq   = [p \in Proc |-> << >>]
  /\ outq  = [p \in Proc |-> << >>]

\* The environment issues a new operation to processor p.
Issue(p) ==
  /\ Len(inq[p]) < InLen
  /\ \E o \in Ops : inq' = [inq EXCEPT ![p] = Append(@, o)]
  /\ UNCHANGED <<mem, cache, outq>>

\* Processor p performs a write lazily: the value is kept only in its cache.
DoWrite(p) ==
  /\ inq[p] # << >>
  /\ Head(inq[p]).op = "W"
  /\ LET o == Head(inq[p]) IN
       cache' = [cache EXCEPT ![p][o.adr] = o.val]
  /\ inq' = [inq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, outq>>

\* Processor p performs a read: answer from cache if dirty, else from memory.
DoRead(p) ==
  /\ inq[p] # << >>
  /\ Head(inq[p]).op = "R"
  /\ Len(outq[p]) < OutLen
  /\ LET a == Head(inq[p]).adr
         d == IF cache[p][a] # ND THEN cache[p][a] ELSE mem[a]
     IN  outq' = [outq EXCEPT ![p] = Append(@, <<a, d>>)]
  /\ inq' = [inq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache>>

\* Processor p lazily flushes a dirty cache entry back to memory.
Flush(p) ==
  /\ \E a \in Addr :
       /\ cache[p][a] # ND
       /\ mem'   = [mem EXCEPT ![a] = cache[p][a]]
       /\ cache' = [cache EXCEPT ![p][a] = ND]
  /\ UNCHANGED <<inq, outq>>

\* The environment consumes a response from processor p.
Consume(p) ==
  /\ outq[p] # << >>
  /\ outq' = [outq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, inq>>

Next ==
  \E p \in Proc :
    \/ Issue(p)
    \/ DoWrite(p)
    \/ DoRead(p)
    \/ Flush(p)
    \/ Consume(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------------

Inv ==
  /\ mem \in [Addr -> Data]
  /\ cache \in [Proc -> [Addr -> Data \cup {ND}]]
  /\ DOMAIN inq = Proc
  /\ DOMAIN outq = Proc
  /\ \A p \in Proc :
       /\ Len(inq[p]) <= InLen
       /\ \A i \in 1..Len(inq[p]) : inq[p][i] \in Ops
       /\ Len(outq[p]) <= OutLen
       /\ \A i \in 1..Len(outq[p]) : outq[p][i] \in OutEntries

=========================================================================================