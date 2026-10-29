------------------------------ MODULE LazyCache ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          ND,        \* distinguished "no data" value
          InitMem,   \* initial memory contents
          QLen       \* maximum queue length

ASSUME /\ ND \notin Val
       /\ InitMem \in [Adr -> Val]
       /\ QLen \in Nat

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

CVal == Val \cup {ND}

\* Messages carried by the input and output queues
InMsg  == Adr \X CVal
OutMsg == CVal

-----------------------------------------------------------------------------
(* Combinatorial estimate of the state space size                           *)

NP == Cardinality(Proc)
NA == Cardinality(Adr)
NV == Cardinality(Val)

Pow(b, e) == LET f[k \in 0..e] == IF k = 0 THEN 1 ELSE b * f[k-1]
             IN  f[e]

\* number of sequences of length 0..QLen over a set of size n
NumSeqs(n) == LET f[k \in 0..QLen] == IF k = 0 THEN 1 ELSE n * f[k-1] + 1
              IN  f[QLen]

StateEstimate ==
    Pow(NV, NA)
  * Pow(NV + 1, NP * NA)
  * Pow(NumSeqs(NA * (NV + 1)), NP)
  * Pow(NumSeqs(NV + 1), NP)

-----------------------------------------------------------------------------
Init ==
    /\ mem = InitMem
    /\ cache \in [Proc -> [Adr -> CVal]]
    /\ \A p \in Proc, a \in Adr : cache[p][a] \in {InitMem[a], ND}
    /\ inq  = [p \in Proc |-> << >>]
    /\ outq = [p \in Proc |-> << >>]
    /\ PrintT(<<"Estimated number of states:", StateEstimate>>)

-----------------------------------------------------------------------------
Stutter == UNCHANGED vars

MemUpdate ==
    /\ \E a \in Adr, v \in Val : mem' = [mem EXCEPT ![a] = v]
    /\ UNCHANGED <<cache, inq, outq>>

CacheUpdate ==
    /\ \E p \in Proc, a \in Adr, v \in CVal :
          cache' = [cache EXCEPT ![p][a] = v]
    /\ UNCHANGED <<mem, inq, outq>>

InqAppend ==
    /\ \E p \in Proc, m \in InMsg :
          /\ Len(inq[p]) < QLen
          /\ inq' = [inq EXCEPT ![p] = Append(@, m)]
    /\ UNCHANGED <<mem, cache, outq>>

OutqAppend ==
    /\ \E p \in Proc, m \in OutMsg :
          /\ Len(outq[p]) < QLen
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
(* Invariant with diagnostic printing on failure                            *)

Check(cond, msg) == IF cond THEN TRUE ELSE Print(msg, FALSE)

Inv ==
    /\ Check(mem \in [Adr -> Val], <<"mem type error", mem>>)
    /\ Check(cache \in [Proc -> [Adr -> CVal]], <<"cache type error", cache>>)
    /\ Check(inq \in [Proc -> Seq(InMsg)], <<"inq type error", inq>>)
    /\ Check(outq \in [Proc -> Seq(OutMsg)], <<"outq type error", outq>>)
    /\ Check(\A p \in Proc : Len(inq[p]) <= QLen,
             <<"inq length bound violated", inq>>)
    /\ Check(\A p \in Proc : Len(outq[p]) <= QLen,
             <<"outq length bound violated", outq>>)

THEOREM Spec => []Inv
=============================================================================