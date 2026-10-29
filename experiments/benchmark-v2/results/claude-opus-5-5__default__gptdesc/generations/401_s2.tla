------------------------------ MODULE LazyCacheTest ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,        \* set of processors
    Adr,         \* set of memory addresses
    Val,         \* set of data values
    ND,          \* distinguished "no data" value for caches
    InitMem,     \* initial data values for memory
    Msg,         \* set of elements that may be placed in queues
    MaxQLen      \* bound on queue lengths

ASSUME /\ ND \notin Val
       /\ InitMem \in [Adr -> Val]
       /\ MaxQLen \in Nat

VARIABLES
    mem,     \* shared memory
    cache,   \* per-processor caches
    inq,     \* per-processor input queues
    outq     \* per-processor output queues

vars == <<mem, cache, inq, outq>>

CVal == Val \cup {ND}

-----------------------------------------------------------------------------
(* Combinatorial estimate of the size of the state space.                 *)

RECURSIVE SeqCount(_)
SeqCount(k) == IF k = 0 THEN 1
               ELSE SeqCount(k - 1) + Cardinality(Msg)^k

MemCount   == Cardinality(Val)^Cardinality(Adr)
CacheCount == Cardinality(CVal)^(Cardinality(Proc) * Cardinality(Adr))
QueueCount == SeqCount(MaxQLen)^(2 * Cardinality(Proc))

StateEstimate == MemCount * CacheCount * QueueCount

-----------------------------------------------------------------------------
(* Initial state                                                          *)

Init ==
    /\ mem = InitMem
    /\ cache \in [Proc -> [Adr -> CVal]]
    /\ \A p \in Proc, a \in Adr : cache[p][a] \in {mem[a], ND}
    /\ inq  = [p \in Proc |-> << >>]
    /\ outq = [p \in Proc |-> << >>]
    /\ PrintT(<<"Estimated number of states:", StateEstimate>>)

-----------------------------------------------------------------------------
(* Actions                                                                *)

Stutter ==
    UNCHANGED vars

MemUpdate ==
    /\ \E a \in Adr, v \in Val : mem' = [mem EXCEPT ![a] = v]
    /\ UNCHANGED <<cache, inq, outq>>

CacheUpdate ==
    /\ \E p \in Proc, a \in Adr, v \in CVal :
          cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<mem, inq, outq>>

InqAppend ==
    /\ \E p \in Proc, m \in Msg :
          /\ Len(inq[p]) < MaxQLen
          /\ inq' = [inq EXCEPT ![p] = Append(@, m)]
    /\ UNCHANGED <<mem, cache, outq>>

OutqAppend ==
    /\ \E p \in Proc, m \in Msg :
          /\ Len(outq[p]) < MaxQLen
          /\ outq' = [outq EXCEPT ![p] = Append(@, m)]
    /\ UNCHANGED <<mem, cache, inq>>

InqTail ==
    /\ \E p \in Proc :
          /\ inq[p] # << >>
          /\ inq' = [inq EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, cache, outq>>

OutqTail ==
    /\ \E p \in Proc :
          /\ outq[p] # << >>
          /\ outq' = [outq EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, cache, inq>>

Next ==
    \/ Stutter
    \/ MemUpdate
    \/ CacheUpdate
    \/ InqAppend
    \/ OutqAppend
    \/ InqTail
    \/ OutqTail

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariant with diagnostic printing on failure                          *)

Check(cond, msg) == IF cond THEN TRUE ELSE Print(msg, FALSE)

QType(q) ==
    /\ q \in [Proc -> Seq(Msg)]
    /\ \A p \in Proc : Len(q[p]) <= MaxQLen

Inv ==
    /\ Check(mem \in [Adr -> Val],
             <<"Inv failed: mem type", mem>>)
    /\ Check(cache \in [Proc -> [Adr -> CVal]],
             <<"Inv failed: cache type", cache>>)
    /\ Check(QType(inq),
             <<"Inv failed: inq type or length", inq>>)
    /\ Check(QType(outq),
             <<"Inv failed: outq type or length", outq>>)

THEOREM Spec => []Inv
=============================================================================