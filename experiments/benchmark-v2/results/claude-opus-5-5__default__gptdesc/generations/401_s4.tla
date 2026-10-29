------------------------------- MODULE LazyCache -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          ND,        \* distinguished "no data" value
          InitMem,   \* initial memory contents: [Adr -> Val]
          QLen       \* maximum queue length

ASSUME /\ ND \notin Val
       /\ InitMem \in [Adr -> Val]
       /\ QLen \in Nat

VARIABLES mem,    \* shared memory
          cache,  \* per-processor caches
          inQ,    \* per-processor input queues
          outQ    \* per-processor output queues

vars == <<mem, cache, inQ, outQ>>

CVal == Val \cup {ND}

Msg == [adr : Adr, val : Val]

BSeq(S) == UNION {[1..n -> S] : n \in 0..QLen}

-----------------------------------------------------------------------------
(* Combinatorial estimate of the state-space size.                         *)

RECURSIVE SumPow(_, _)
SumPow(b, n) == IF n = 0 THEN 1 ELSE b^n + SumPow(b, n - 1)

NumAdr  == Cardinality(Adr)
NumProc == Cardinality(Proc)
NumQ    == SumPow(Cardinality(Msg), QLen)

StateEstimate ==
    (Cardinality(Val) ^ NumAdr)
      * ((Cardinality(Val) + 1) ^ (NumAdr * NumProc))
      * (NumQ ^ (2 * NumProc))

-----------------------------------------------------------------------------
Init ==
    /\ Print(<<"Estimated number of states:", StateEstimate>>, TRUE)
    /\ mem = InitMem
    /\ cache \in [Proc -> {f \in [Adr -> CVal] :
                             \A a \in Adr : f[a] \in {InitMem[a], ND}}]
    /\ inQ  = [p \in Proc |-> << >>]
    /\ outQ = [p \in Proc |-> << >>]

Stutter == UNCHANGED vars

MemUpdate ==
    \E a \in Adr, v \in Val :
        /\ mem' = [mem EXCEPT ![a] = v]
        /\ UNCHANGED <<cache, inQ, outQ>>

CacheUpdate ==
    \E p \in Proc, a \in Adr, v \in CVal :
        /\ cache' = [cache EXCEPT ![p][a] = v]
        /\ UNCHANGED <<mem, inQ, outQ>>

InQAppend ==
    \E p \in Proc, m \in Msg :
        /\ Len(inQ[p]) < QLen
        /\ inQ' = [inQ EXCEPT ![p] = Append(@, m)]
        /\ UNCHANGED <<mem, cache, outQ>>

OutQAppend ==
    \E p \in Proc, m \in Msg :
        /\ Len(outQ[p]) < QLen
        /\ outQ' = [outQ EXCEPT ![p] = Append(@, m)]
        /\ UNCHANGED <<mem, cache, inQ>>

InQTail ==
    \E p \in Proc :
        /\ inQ[p] /= << >>
        /\ inQ' = [inQ EXCEPT ![p] = Tail(@)]
        /\ UNCHANGED <<mem, cache, outQ>>

OutQTail ==
    \E p \in Proc :
        /\ outQ[p] /= << >>
        /\ outQ' = [outQ EXCEPT ![p] = Tail(@)]
        /\ UNCHANGED <<mem, cache, inQ>>

Next ==
    \/ Stutter
    \/ MemUpdate
    \/ CacheUpdate
    \/ InQAppend
    \/ OutQAppend
    \/ InQTail
    \/ OutQTail

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariant with diagnostic output when a conjunct fails.                 *)

Check(cond, msg) == IF cond THEN TRUE ELSE Print(msg, FALSE)

Inv ==
    /\ Check(mem \in [Adr -> Val], <<"Inv failed: mem type", mem>>)
    /\ Check(cache \in [Proc -> [Adr -> CVal]], <<"Inv failed: cache type", cache>>)
    /\ Check(inQ \in [Proc -> Seq(Msg)], <<"Inv failed: inQ type", inQ>>)
    /\ Check(outQ \in [Proc -> Seq(Msg)], <<"Inv failed: outQ type", outQ>>)
    /\ Check(\A p \in Proc : Len(inQ[p]) <= QLen,
             <<"Inv failed: inQ length bound", inQ>>)
    /\ Check(\A p \in Proc : Len(outQ[p]) <= QLen,
             <<"Inv failed: outQ length bound", outQ>>)

THEOREM Spec => []Inv
=============================================================================