------------------------------- MODULE LazyCacheFingerprint -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Data, InitData, Addr, N, InLen, OutLen, ND

VARIABLES mem, c, in, out

vars == <<mem, c, in, out>>

Proc == 1..N

CVal == Data \cup {ND}

Ops == [type : {"Rd"}, adr : Addr] \cup [type : {"Wr"}, adr : Addr, val : Data]

OutElt == Data \X Addr

BSeq(S, n) == UNION {[1..k -> S] : k \in 0..n}

(* Sum_{i=0..n} b^i *)
GeomSum(b, n) ==
  LET f[k \in 0..n] == IF k = 0 THEN 1 ELSE 1 + b * f[k-1]
  IN  f[n]

Pow(b, n) ==
  LET f[k \in 0..n] == IF k = 0 THEN 1 ELSE b * f[k-1]
  IN  f[n]

NumStates ==
  Pow(Cardinality(Data), Cardinality(Addr))
  * Pow(Cardinality(Data) + 1, Cardinality(Addr) * N)
  * Pow(GeomSum(Cardinality(Ops), InLen), N)
  * Pow(GeomSum(Cardinality(OutElt), OutLen), N)

Init ==
  /\ mem \in [Addr -> InitData]
  /\ c \in {f \in [Proc -> [Addr -> CVal]] :
               \A p \in Proc, a \in Addr : f[p][a] \in {mem[a], ND}}
  /\ in = [p \in Proc |-> << >>]
  /\ out = [p \in Proc |-> << >>]
  /\ PrintT(<<"Total number of reachable states should be", NumStates>>)

NextMem ==
  {mem} \cup {[mem EXCEPT ![a] = d] : a \in Addr, d \in Data}

NextC ==
  {c} \cup {[c EXCEPT ![p][a] = v] : p \in Proc, a \in Addr, v \in CVal}

NextIn ==
  {in}
  \cup {[in EXCEPT ![p] = Append(in[p], op)] :
          p \in {q \in Proc : Len(in[q]) < InLen}, op \in Ops}
  \cup {[in EXCEPT ![p] = Tail(in[p])] :
          p \in {q \in Proc : Len(in[q]) > 0}}

NextOut ==
  {out}
  \cup {[out EXCEPT ![p] = Append(out[p], e)] :
          p \in {q \in Proc : Len(out[q]) < OutLen}, e \in OutElt}
  \cup {[out EXCEPT ![p] = Tail(out[p])] :
          p \in {q \in Proc : Len(out[q]) > 0}}

Next ==
  /\ mem' \in NextMem
  /\ c' \in NextC
  /\ in' \in NextIn
  /\ out' \in NextOut

Spec == Init /\ [][Next]_vars

Check(cond, msg) == IF cond THEN TRUE ELSE PrintT(msg) /\ FALSE

Inv ==
  /\ Check(mem \in [Addr -> Data], "Inv: mem type conjunct fails")
  /\ Check(c \in [Proc -> [Addr -> CVal]], "Inv: c type conjunct fails")
  /\ Check(in \in [Proc -> Seq(Ops)], "Inv: in type conjunct fails")
  /\ Check(out \in [Proc -> Seq(OutElt)], "Inv: out type conjunct fails")
  /\ Check(\A p \in Proc : Len(in[p]) <= InLen, "Inv: in length conjunct fails")
  /\ Check(\A p \in Proc : Len(out[p]) <= OutLen, "Inv: out length conjunct fails")

=============================================================================