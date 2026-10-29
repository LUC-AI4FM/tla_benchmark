----- MODULE CacheService -----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Data, InitData, Addr, N, InLen, OutLen, ND

ASSUME /\ N \in Nat \ {0}
       /\ InLen \in Nat
       /\ OutLen \in Nat
       /\ InitData \subseteq Data
       /\ ND \notin Data

VARIABLES mem, view, inq, outq

vars == <<mem, view, inq, outq>>

Proc == 1..N

Val == Data \cup {ND}

Msg == [adr : Addr, val : Val]

BSeq(S, max) == UNION {[1..k -> S] : k \in 0..max}

TypeOK ==
  /\ mem \in [Addr -> Data]
  /\ view \in [Proc -> [Addr -> Val]]
  /\ inq \in [Proc -> Seq(Msg)]
  /\ outq \in [Proc -> Seq(Msg)]
  /\ \A p \in Proc : Len(inq[p]) <= InLen /\ Len(outq[p]) <= OutLen

Consistent ==
  \A p \in Proc : \A a \in Addr : view[p][a] \in {mem[a], ND}

Inv == TypeOK /\ Consistent

Init ==
  /\ mem \in [Addr -> InitData]
  /\ view \in [Proc -> [Addr -> Val]]
  /\ \A p \in Proc : \A a \in Addr : view[p][a] \in {mem[a], ND}
  /\ inq = [p \in Proc |-> << >>]
  /\ outq = [p \in Proc |-> << >>]

MemWrite(a, d) ==
  /\ mem' = [mem EXCEPT ![a] = d]
  /\ view' = [p \in Proc |->
                [view[p] EXCEPT ![a] = IF @ = d THEN d ELSE ND]]
  /\ UNCHANGED <<inq, outq>>

LocalWrite(p, a, v) ==
  /\ v \in {mem[a], ND}
  /\ view' = [view EXCEPT ![p][a] = v]
  /\ UNCHANGED <<mem, inq, outq>>

EnqIn(p, m) ==
  /\ Len(inq[p]) < InLen
  /\ inq' = [inq EXCEPT ![p] = Append(@, m)]
  /\ UNCHANGED <<mem, view, outq>>

DeqIn(p) ==
  /\ inq[p] # << >>
  /\ inq' = [inq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, view, outq>>

EnqOut(p, m) ==
  /\ Len(outq[p]) < OutLen
  /\ outq' = [outq EXCEPT ![p] = Append(@, m)]
  /\ UNCHANGED <<mem, view, inq>>

DeqOut(p) ==
  /\ outq[p] # << >>
  /\ outq' = [outq EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, view, inq>>

Next ==
  \/ \E a \in Addr, d \in Data : MemWrite(a, d)
  \/ \E p \in Proc, a \in Addr, v \in Val : LocalWrite(p, a, v)
  \/ \E p \in Proc, m \in Msg : EnqIn(p, m)
  \/ \E p \in Proc : DeqIn(p)
  \/ \E p \in Proc, m \in Msg : EnqOut(p, m)
  \/ \E p \in Proc : DeqOut(p)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
=====