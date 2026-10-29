------------------------------- MODULE test27 -------------------------------
(***************************************************************************)
(* A fingerprint / state-count test for TLC.  It is loosely modeled on a   *)
(* "LazyCache" structure, but its real purpose is to check that TLC        *)
(* enumerates exactly the expected number of distinct states.  The         *)
(* expected count is printed by Init.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Adr,          \* set of addresses
          Data,         \* set of data values
          InitData,     \* initial memory contents, an element of [Adr -> Data]
          NumProcs,     \* number of processors
          MaxInQLen,    \* maximum length of each input queue
          MaxOutQLen    \* maximum length of each output queue

ASSUME /\ InitData \in [Adr -> Data]
       /\ NumProcs \in Nat
       /\ MaxInQLen \in Nat
       /\ MaxOutQLen \in Nat

VARIABLES mem, c, in, out

vars == <<mem, c, in, out>>

Proc == 1..NumProcs

ND == CHOOSE v : v \notin Data          \* the "no-data" sentinel

CData == Data \cup {ND}

(* Operations: plain (data, address) pairs, plus a tagged write variant.  *)
Op == (Data \X Adr) \cup ({"Wr"} \X Data \X Adr)

Result == Data

(* Bounded sequences over a set S with length at most n. *)
BSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}

(* Number of sequences of length <= n over a set of k elements. *)
NumSeqs(k, n) ==
  LET f[i \in 0..n] == IF i = 0 THEN 1 ELSE 1 + k * f[i-1]
  IN  f[n]

(* Expected number of distinct reachable states. *)
ExpectedStates ==
  LET nA == Cardinality(Adr)
      nD == Cardinality(Data)
      nO == Cardinality(Op)
  IN  (nD ^ nA)
        * ((nD + 1) ^ (nA * NumProcs))
        * (NumSeqs(nO, MaxInQLen) ^ NumProcs)
        * (NumSeqs(nD, MaxOutQLen) ^ NumProcs)

-----------------------------------------------------------------------------
Init ==
  /\ mem = InitData
  /\ c \in [Proc -> {f \in [Adr -> CData] :
                        \A a \in Adr : f[a] = mem[a] \/ f[a] = ND}]
  /\ in  = [p \in Proc |-> << >>]
  /\ out = [p \in Proc |-> << >>]
  /\ PrintT(<<"Should find", ExpectedStates, "distinct states">>)

MemWrite ==
  /\ \E a \in Adr, d \in Data : mem' = [mem EXCEPT ![a] = d]
  /\ UNCHANGED <<c, in, out>>

CacheSet ==
  /\ \E p \in Proc, a \in Adr, d \in CData : c' = [c EXCEPT ![p][a] = d]
  /\ UNCHANGED <<mem, in, out>>

InAppend ==
  /\ \E p \in Proc, op \in Op :
        /\ Len(in[p]) < MaxInQLen
        /\ in' = [in EXCEPT ![p] = Append(@, op)]
  /\ UNCHANGED <<mem, c, out>>

InRemove ==
  /\ \E p \in Proc :
        /\ in[p] # << >>
        /\ in' = [in EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, c, out>>

OutAppend ==
  /\ \E p \in Proc, r \in Result :
        /\ Len(out[p]) < MaxOutQLen
        /\ out' = [out EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED <<mem, c, in>>

OutRemove ==
  /\ \E p \in Proc :
        /\ out[p] # << >>
        /\ out' = [out EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, c, in>>

Next == MemWrite \/ CacheSet \/ InAppend \/ InRemove \/ OutAppend \/ OutRemove

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
Check(b, msg) == IF b THEN TRUE ELSE PrintT(msg) /\ FALSE

Inv ==
  /\ Check(mem \in [Adr -> Data], "Inv: mem type failed")
  /\ Check(c \in [Proc -> [Adr -> CData]], "Inv: c type failed")
  /\ Check(in \in [Proc -> Seq(Op)], "Inv: in type failed")
  /\ Check(out \in [Proc -> Seq(Result)], "Inv: out type failed")
  /\ Check(\A p \in Proc : Len(in[p]) <= MaxInQLen,
           "Inv: in length bound failed")
  /\ Check(\A p \in Proc : Len(out[p]) <= MaxOutQLen,
           "Inv: out length bound failed")

THEOREM Spec => []Inv
=============================================================================