------------------------------- MODULE test27 -------------------------------
(***************************************************************************)
(* A fingerprint / state-count test for TLC, modelled loosely on a         *)
(* "LazyCache" structure.  The next-state relation is deliberately         *)
(* permissive so that the number of reachable distinct states can be       *)
(* computed in closed form and compared against what TLC reports.          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Data, InitData, Addr, N, InLen, OutLen, ND

VARIABLES mem, c, in, out

vars == <<mem, c, in, out>>

Proc == 1..N

(* Operations: read requests <<d, a>> and tagged writes <<"W", d, a>>     *)
Op == (Data \X Addr) \cup ({"W"} \X Data \X Addr)

(* Output results *)
Res == Data

(* Bounded sequences over S of length at most n *)
BSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

(* Number of sequences over a set of size s with length at most n *)
GeomSum(s, n) ==
  LET f[k \in 0..n] == IF k = 0 THEN 1 ELSE f[k-1] + s^k
  IN  f[n]

NumStates ==
    (Cardinality(Data) ^ Cardinality(Addr))
  * ((Cardinality(Data) + 1) ^ (Cardinality(Addr) * N))
  * (GeomSum(Cardinality(Op), InLen) ^ N)
  * (GeomSum(Cardinality(Res), OutLen) ^ N)

TypeOK ==
  /\ mem \in [Addr -> Data]
  /\ c \in [Proc -> [Addr -> Data \cup {ND}]]
  /\ in \in [Proc -> Seq(Op)]
  /\ out \in [Proc -> Seq(Res)]

Init ==
  /\ mem \in [Addr -> InitData]
  /\ c \in [Proc -> { f \in [Addr -> Data \cup {ND}] :
                         \A a \in Addr : f[a] = ND \/ f[a] = mem[a] }]
  /\ in = [p \in Proc |-> << >>]
  /\ out = [p \in Proc |-> << >>]
  /\ PrintT(<<"Number of reachable states should be", NumStates>>)

MemWrite ==
  /\ \E a \in Addr, d \in Data : mem' = [mem EXCEPT ![a] = d]
  /\ UNCHANGED <<c, in, out>>

CacheSet ==
  /\ \E p \in Proc, a \in Addr, d \in Data \cup {ND} :
        c' = [c EXCEPT ![p][a] = d]
  /\ UNCHANGED <<mem, in, out>>

InAppend ==
  /\ \E p \in Proc, op \in Op :
        /\ Len(in[p]) < InLen
        /\ in' = [in EXCEPT ![p] = Append(@, op)]
  /\ UNCHANGED <<mem, c, out>>

InRemove ==
  /\ \E p \in Proc :
        /\ in[p] # << >>
        /\ in' = [in EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, c, out>>

OutAppend ==
  /\ \E p \in Proc, r \in Res :
        /\ Len(out[p]) < OutLen
        /\ out' = [out EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED <<mem, c, in>>

OutRemove ==
  /\ \E p \in Proc :
        /\ out[p] # << >>
        /\ out' = [out EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, c, in>>

Next ==
  \/ MemWrite
  \/ CacheSet
  \/ InAppend
  \/ InRemove
  \/ OutAppend
  \/ OutRemove

Spec == Init /\ [][Next]_vars

Inv ==
  /\ IF mem \in [Addr -> Data] THEN TRUE
       ELSE Print("Inv failed: mem type", FALSE)
  /\ IF c \in [Proc -> [Addr -> Data \cup {ND}]] THEN TRUE
       ELSE Print("Inv failed: c type", FALSE)
  /\ IF in \in [Proc -> BSeq(Op, InLen)] THEN TRUE
       ELSE Print("Inv failed: in type or length bound", FALSE)
  /\ IF out \in [Proc -> BSeq(Res, OutLen)] THEN TRUE
       ELSE Print("Inv failed: out type or length bound", FALSE)
=============================================================================