---------------------------- MODULE LazyCache ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          ND,        \* distinguished "no data" value
          InitData,  \* initial memory contents
          QLen       \* maximum queue length

ASSUME /\ ND \notin Val
       /\ InitData \in [Adr -> Val]
       /\ QLen \in Nat

VARIABLES memory, cache, inQ, outQ

vars == <<memory, cache, inQ, outQ>>

CVal == Val \cup {ND}

Msg == [adr : Adr, val : CVal]

BoundedSeq(S, n) == UNION {[1..k -> S] : k \in 0..n}

\* Combinatorial estimate of the number of reachable states
NumQueues(n) == LET m == Cardinality(Msg)
                IN  LET Sum[k \in 0..n] == IF k = 0 THEN 1
                                           ELSE Sum[k-1] + m^k
                    IN Sum[n]

StateEstimate ==
    (Cardinality(Val) ^ Cardinality(Adr))
  * (Cardinality(CVal) ^ (Cardinality(Adr) * Cardinality(Proc)))
  * (NumQueues(QLen) ^ (2 * Cardinality(Proc)))

-----------------------------------------------------------------------------
Init ==
    /\ memory = InitData
    /\ cache \in [Proc -> {f \in [Adr -> CVal] :
                             \A a \in Adr : f[a] \in {InitData[a], ND}}]
    /\ inQ  = [p \in Proc |-> << >>]
    /\ outQ = [p \in Proc |-> << >>]
    /\ Print(<<"Estimated number of states: ", StateEstimate>>, TRUE)

-----------------------------------------------------------------------------
Stutter == UNCHANGED vars

MemoryUpdate ==
    \E a \in Adr, v \in Val :
        /\ memory' = [memory EXCEPT ![a] = v]
        /\ UNCHANGED <<cache, inQ, outQ>>

CacheUpdate ==
    \E p \in Proc, a \in Adr, v \in CVal :
        /\ cache' = [cache EXCEPT ![p][a] = v]
        /\ UNCHANGED <<memory, inQ, outQ>>

InQAppend ==
    \E p \in Proc, m \in Msg :
        /\ Len(inQ[p]) < QLen
        /\ inQ' = [inQ EXCEPT ![p] = Append(@, m)]
        /\ UNCHANGED <<memory, cache, outQ>>

OutQAppend ==
    \E p \in Proc, m \in Msg :
        /\ Len(outQ[p]) < QLen
        /\ outQ' = [outQ EXCEPT ![p] = Append(@, m)]
        /\ UNCHANGED <<memory, cache, inQ>>

InQTail ==
    \E p \in Proc :
        /\ inQ[p] # << >>
        /\ inQ' = [inQ EXCEPT ![p] = Tail(@)]
        /\ UNCHANGED <<memory, cache, outQ>>

OutQTail ==
    \E p \in Proc :
        /\ outQ[p] # << >>
        /\ outQ' = [outQ EXCEPT ![p] = Tail(@)]
        /\ UNCHANGED <<memory, cache, inQ>>

Next ==
    \/ Stutter
    \/ MemoryUpdate
    \/ CacheUpdate
    \/ InQAppend
    \/ OutQAppend
    \/ InQTail
    \/ OutQTail

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
Check(cond, msg) == IF cond THEN TRUE ELSE Print(msg, FALSE)

Inv ==
    /\ Check(memory \in [Adr -> Val],
             "Inv failure: memory has wrong type")
    /\ Check(cache \in [Proc -> [Adr -> CVal]],
             "Inv failure: cache has wrong type")
    /\ Check(inQ \in [Proc -> Seq(Msg)],
             "Inv failure: inQ has wrong type")
    /\ Check(outQ \in [Proc -> Seq(Msg)],
             "Inv failure: outQ has wrong type")
    /\ Check(\A p \in Proc : Len(inQ[p]) <= QLen,
             "Inv failure: inQ exceeds QLen")
    /\ Check(\A p \in Proc : Len(outQ[p]) <= QLen,
             "Inv failure: outQ exceeds QLen")

THEOREM Spec => []Inv
=============================================================================