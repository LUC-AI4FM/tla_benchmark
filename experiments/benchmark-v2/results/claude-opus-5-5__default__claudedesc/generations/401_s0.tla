---------------------------- MODULE LazyCacheFingerprintTest ----------------------------
(***************************************************************************)
(* A fingerprint / regression test for TLC modeled on a simplified lazy   *)
(* cache.  It is not a real protocol.  Next allows essentially arbitrary  *)
(* type-correct changes, so the reachable state space is exactly the set  *)
(* of type-correct states.  Its size is computed analytically and printed *)
(* in Init so it can be compared with TLC's distinct-state count.         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Adr,        \* set of addresses
          Data,       \* set of data values
          InitData,   \* subset of Data used for initial memory contents
          ND,         \* the distinguished "not-dirty" cache value
          NumProcs,   \* number of processors
          InQLen,     \* maximum length of each input queue
          OutQLen     \* maximum length of each output queue

ASSUME /\ InitData \subseteq Data
       /\ InitData # {}
       /\ ND \notin Data
       /\ NumProcs \in Nat \ {0}
       /\ InQLen \in Nat
       /\ OutQLen \in Nat
       /\ IsFiniteSet(Adr)
       /\ IsFiniteSet(Data)

VARIABLES mem, c, in, out

vars == <<mem, c, in, out>>

Proc == 1..NumProcs

CacheVal == Data \cup {ND}

\* Operations that can appear in input queues
RdOps == [type : {"Rd"}, adr : Adr]
WrOps == [type : {"Wr"}, adr : Adr, val : Data]
Ops   == RdOps \cup WrOps

\* Entries of output queues: data/address pairs
OutEntries == Data \X Adr

(***************************************************************************)
(* Analytic computation of the number of reachable states.                 *)
(***************************************************************************)
RECURSIVE SeqCount(_, _)
\* Number of sequences over a k-element set with length at most n
SeqCount(k, n) == IF n = 0 THEN 1 ELSE 1 + k * SeqCount(k, n - 1)

NA == Cardinality(Adr)
ND_ == Cardinality(Data)

NumOps == NA + NA * ND_
NumOutEntries == ND_ * NA

MemStates == ND_ ^ NA
CacheStates == (ND_ + 1) ^ (NA * NumProcs)
InStates == SeqCount(NumOps, InQLen) ^ NumProcs
OutStates == SeqCount(NumOutEntries, OutQLen) ^ NumProcs

TotalStates == MemStates * CacheStates * InStates * OutStates

(***************************************************************************)
(* Initial predicate                                                       *)
(***************************************************************************)
Init ==
  /\ mem \in [Adr -> InitData]
  /\ c \in { f \in [Proc -> [Adr -> CacheVal]] :
               \A p \in Proc : \A a \in Adr : f[p][a] \in {mem[a], ND} }
  /\ in = [p \in Proc |-> << >>]
  /\ out = [p \in Proc |-> << >>]
  /\ PrintT(<<"Total number of reachable states should be", TotalStates>>)

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Stutter == UNCHANGED vars

MemWrite ==
  /\ \E a \in Adr, d \in Data : mem' = [mem EXCEPT ![a] = d]
  /\ UNCHANGED <<c, in, out>>

CacheUpdate ==
  /\ \E p \in Proc, a \in Adr, v \in CacheVal :
        c' = [c EXCEPT ![p][a] = v]
  /\ UNCHANGED <<mem, in, out>>

InAppend ==
  /\ \E p \in Proc, op \in Ops :
        /\ Len(in[p]) < InQLen
        /\ in' = [in EXCEPT ![p] = Append(@, op)]
  /\ UNCHANGED <<mem, c, out>>

InDequeue ==
  /\ \E p \in Proc :
        /\ in[p] # << >>
        /\ in' = [in EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, c, out>>

OutAppend ==
  /\ \E p \in Proc, e \in OutEntries :
        /\ Len(out[p]) < OutQLen
        /\ out' = [out EXCEPT ![p] = Append(@, e)]
  /\ UNCHANGED <<mem, c, in>>

OutDequeue ==
  /\ \E p \in Proc :
        /\ out[p] # << >>
        /\ out' = [out EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, c, in>>

Next ==
  \/ Stutter
  \/ MemWrite
  \/ CacheUpdate
  \/ InAppend
  \/ InDequeue
  \/ OutAppend
  \/ OutDequeue

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariant: type correctness and queue bounds, with diagnostics.         *)
(***************************************************************************)
Inv ==
  /\ \/ mem \in [Adr -> Data]
     \/ PrintT("Inv failed: mem has wrong type") /\ FALSE
  /\ \/ c \in [Proc -> [Adr -> CacheVal]]
     \/ PrintT("Inv failed: c has wrong type") /\ FALSE
  /\ \/ in \in [Proc -> Seq(Ops)]
     \/ PrintT("Inv failed: in has wrong type") /\ FALSE
  /\ \/ out \in [Proc -> Seq(OutEntries)]
     \/ PrintT("Inv failed: out has wrong type") /\ FALSE
  /\ \/ \A p \in Proc : Len(in[p]) <= InQLen
     \/ PrintT("Inv failed: an input queue exceeds InQLen") /\ FALSE
  /\ \/ \A p \in Proc : Len(out[p]) <= OutQLen
     \/ PrintT("Inv failed: an output queue exceeds OutQLen") /\ FALSE

THEOREM Spec => []Inv
=============================================================================