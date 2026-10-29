---------------------------- MODULE LazyCache ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Data, InitData, Addr, N, InLen, OutLen, ND

ASSUME ND \notin Data
ASSUME InitData \subseteq Data
ASSUME N \in Nat /\ InLen \in Nat /\ OutLen \in Nat

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

Proc == 1..N

CacheVal == Data \cup {ND}

QEntry == Addr \X Data

-----------------------------------------------------------------------------

Init ==
  /\ mem \in [Addr -> InitData]
  /\ cache \in {c \in [Proc -> [Addr -> CacheVal]] :
                  \A p \in Proc, a \in Addr : c[p][a] \in {mem[a], ND}}
  /\ inq = [p \in Proc |-> << >>]
  /\ outq = [p \in Proc |-> << >>]
  /\ PrintT(<<"Estimated number of initial states:",
              (Cardinality(InitData) ^ Cardinality(Addr))
                * (2 ^ (N * Cardinality(Addr)))>>)

MemUpdate ==
  /\ \E a \in Addr, d \in Data : mem' = [mem EXCEPT ![a] = d]
  /\ UNCHANGED <<cache, inq, outq>>

CacheUpdate ==
  /\ \E p \in Proc, a \in Addr, v \in CacheVal :
        cache' = [cache EXCEPT ![p][a] = v]
  /\ UNCHANGED <<mem, inq, outq>>

InAppend ==
  /\ \E p \in Proc, e \in QEntry :
        /\ Len(inq[p]) < InLen
        /\ inq' = [inq EXCEPT ![p] = Append(@, e)]
  /\ UNCHANGED <<mem, cache, outq>>

OutAppend ==
  /\ \E p \in Proc, e \in QEntry :
        /\ Len(outq[p]) < OutLen
        /\ outq' = [outq EXCEPT ![p] = Append(@, e)]
  /\ UNCHANGED <<mem, cache, inq>>

InTail ==
  /\ \E p \in Proc :
        /\ inq[p] # << >>
        /\ inq' = [inq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, outq>>

OutTail ==
  /\ \E p \in Proc :
        /\ outq[p] # << >>
        /\ outq' = [outq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, cache, inq>>

Next ==
  \/ UNCHANGED vars
  \/ MemUpdate
  \/ CacheUpdate
  \/ InAppend
  \/ OutAppend
  \/ InTail
  \/ OutTail

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Check(cond, msg) == IF cond THEN TRUE ELSE Print(msg, FALSE)

Inv ==
  /\ Check(mem \in [Addr -> Data], <<"mem type error", mem>>)
  /\ Check(cache \in [Proc -> [Addr -> CacheVal]], <<"cache type error", cache>>)
  /\ Check(inq \in [Proc -> Seq(QEntry)], <<"inq type error", inq>>)
  /\ Check(outq \in [Proc -> Seq(QEntry)], <<"outq type error", outq>>)
  /\ Check(\A p \in Proc : Len(inq[p]) <= InLen, <<"inq too long", inq>>)
  /\ Check(\A p \in Proc : Len(outq[p]) <= OutLen, <<"outq too long", outq>>)

=============================================================================