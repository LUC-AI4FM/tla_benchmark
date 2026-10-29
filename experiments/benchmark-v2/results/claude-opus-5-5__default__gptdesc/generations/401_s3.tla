------------------------------ MODULE LazyCache ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          ND,        \* distinguished "no data" value
          QLen       \* maximum queue length

ASSUME ND \notin Val
ASSUME QLen \in Nat

VARIABLES mem, cache, inq, outq

vars == <<mem, cache, inq, outq>>

CVal == Val \cup {ND}

Msg == [adr : Adr, val : CVal]

BSeq(S, n) == UNION {[1..k -> S] : k \in 0..n}

-----------------------------------------------------------------------------
(* Combinatorial estimate of the number of initial states:                 *)
(*   |Val|^|Adr| choices of memory times 2^(|Proc|*|Adr|) cache choices.   *)

Pow(b, e) == IF e = 0 THEN 1 ELSE LET f[i \in 0..e] ==
                                        IF i = 0 THEN 1 ELSE b * f[i-1]
                                    IN f[e]

InitEstimate ==
  Pow(Cardinality(Val), Cardinality(Adr)) *
  Pow(2, Cardinality(Proc) * Cardinality(Adr))

Init ==
  /\ mem \in [Adr -> Val]
  /\ cache \in [Proc -> [Adr -> CVal]]
  /\ \A p \in Proc, a \in Adr : cache[p][a] \in {mem[a], ND}
  /\ inq = [p \in Proc |-> << >>]
  /\ outq = [p \in Proc |-> << >>]
  /\ PrintT(<<"Estimated number of initial states:", InitEstimate>>)

-----------------------------------------------------------------------------
Stutter == UNCHANGED vars

MemUpdate ==
  \E a \in Adr, v \in Val :
     /\ mem' = [mem EXCEPT ![a] = v]
     /\ UNCHANGED <<cache, inq, outq>>

CacheUpdate ==
  \E p \in Proc, a \in Adr, v \in CVal :
     /\ cache' = [cache EXCEPT ![p][a] = v]
     /\ UNCHANGED <<mem, inq, outq>>

InqAppend ==
  \E p \in Proc, m \in Msg :
     /\ Len(inq[p]) < QLen
     /\ inq' = [inq EXCEPT ![p] = Append(@, m)]
     /\ UNCHANGED <<mem, cache, outq>>

OutqAppend ==
  \E p \in Proc, m \in Msg :
     /\ Len(outq[p]) < QLen
     /\ outq' = [outq EXCEPT ![p] = Append(@, m)]
     /\ UNCHANGED <<mem, cache, inq>>

InqTail ==
  \E p \in Proc :
     /\ inq[p] # << >>
     /\ inq' = [inq EXCEPT ![p] = Tail(@)]
     /\ UNCHANGED <<mem, cache, outq>>

OutqTail ==
  \E p \in Proc :
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
(* Invariant with diagnostic printing when a conjunct fails.               *)

Check(cond, msg) == IF cond THEN TRUE ELSE Print(msg, FALSE)

Inv ==
  /\ Check(mem \in [Adr -> Val], <<"Inv failed: mem type", mem>>)
  /\ Check(cache \in [Proc -> [Adr -> CVal]], <<"Inv failed: cache type", cache>>)
  /\ Check(inq \in [Proc -> Seq(Msg)], <<"Inv failed: inq type", inq>>)
  /\ Check(outq \in [Proc -> Seq(Msg)], <<"Inv failed: outq type", outq>>)
  /\ Check(\A p \in Proc : Len(inq[p]) <= QLen, <<"Inv failed: inq length", inq>>)
  /\ Check(\A p \in Proc : Len(outq[p]) <= QLen, <<"Inv failed: outq length", outq>>)

THEOREM Spec => []Inv
=============================================================================