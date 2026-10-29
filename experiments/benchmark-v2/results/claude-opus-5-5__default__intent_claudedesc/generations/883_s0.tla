------------------------------ MODULE SerialMemory ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,     \* set of processes
          Adr,      \* set of memory addresses
          Val,      \* set of memory values
          Reg,      \* set of registers available to each process
          InitMem   \* initial memory contents: a function Adr -> Val

ASSUME InitMem \in [Adr -> Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Requests, register contents and operation records                       *)
(***************************************************************************)
RdRequest == [op : {"Rd"}, adr : Adr]
WrRequest == [op : {"Wr"}, adr : Adr, val : Val]
Request   == RdRequest \cup WrRequest

\* A register is either free (holding the last value returned, if any) or
\* busy holding exactly one pending request.
RegContents == [state : {"Free"}, val : Val \cup {NoVal}]
                 \cup [state : {"Busy"}, req : Request]

\* An operation record in a process's operation queue.
\*   val  : for reads, the value returned (NoVal while pending)
\*   done : whether the operation has been responded to
OpRecord == [req : Request, reg : Reg, val : Val \cup {NoVal}, done : BOOLEAN]

\* The universe of operation identifiers.
OpIdUniverse == [proc : Proc, idx : Nat \ {0}]

VARIABLES regFile,   \* regFile[p][r] : contents of register r of process p
          opQ,       \* opQ[p] : sequence of all operations issued by p
          opOrder    \* the ordering relation established so far on op ids

vars == <<regFile, opQ, opOrder>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)
OpIdsOf(q) == {[proc |-> p, idx |-> i] : p \in Proc, i \in 1..Len(q[p])}

OpIds == OpIdsOf(opQ)

OpOf(q, oi) == q[oi.proc][oi.idx]

IsStrictTotalOrder(R, S) ==
  /\ \A a \in S : <<a, a>> \notin R
  /\ \A a, b, c \in S : (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R
  /\ \A a, b \in S : a # b => (<<a, b>> \in R \/ <<b, a>> \in R)

\* There exists a total order of all operations that extends oord, respects
\* program order, and in which every completed read returns the value of
\* the most recent preceding write to the same address (or initial memory).
Serializable(q, oord) ==
  LET ids == OpIdsOf(q) IN
  \E R \in SUBSET (ids \X ids) :
    /\ IsStrictTotalOrder(R, ids)
    /\ oord \subseteq R
    /\ \A oi, oj \in ids :
          (oi.proc = oj.proc /\ oi.idx < oj.idx) => <<oi, oj>> \in R
    /\ \A oi \in ids :
          LET o == OpOf(q, oi) IN
          (o.req.op = "Rd" /\ o.val # NoVal) =>
            LET prevW == {ow \in ids :
                            /\ <<ow, oi>> \in R
                            /\ OpOf(q, ow).req.op = "Wr"
                            /\ OpOf(q, ow).req.adr = o.req.adr}
            IN IF prevW = {}
                 THEN o.val = InitMem[o.req.adr]
                 ELSE \E w \in prevW :
                        /\ OpOf(q, w).req.val = o.val
                        /\ \A w2 \in prevW : w2 = w \/ <<w2, w>> \in R

\* opOrder may only grow, and must remain serializable.
UpdateOpOrder ==
  /\ opOrder' \in SUBSET (OpIdsOf(opQ') \X OpIdsOf(opQ'))
  /\ opOrder \subseteq opOrder'
  /\ Serializable(opQ', opOrder')

\* Index of the pending operation of process p using register r.
PendingIdx(p, r) ==
  {i \in 1..Len(opQ[p]) : opQ[p][i].reg = r /\ ~opQ[p][i].done}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> [state |-> "Free", val |-> NoVal]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
IssueRequest(p, req, r) ==
  /\ regFile[p][r].state = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = [state |-> "Busy", req |-> req]]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r, val |-> NoVal, done |-> FALSE])]
  /\ UpdateOpOrder

RespondToWr(p, r) ==
  /\ regFile[p][r].state = "Busy"
  /\ regFile[p][r].req.op = "Wr"
  /\ \E i \in PendingIdx(p, r) :
        opQ' = [opQ EXCEPT ![p][i].done = TRUE]
  /\ regFile' = [regFile EXCEPT ![p][r] = [state |-> "Free", val |-> NoVal]]
  /\ UpdateOpOrder

RespondToRd(p, r) ==
  /\ regFile[p][r].state = "Busy"
  /\ regFile[p][r].req.op = "Rd"
  /\ LET a == regFile[p][r].req.adr IN
     \E i \in PendingIdx(p, r), v \in Val :
        /\ \/ v = InitMem[a]
           \/ \E q \in Proc : \E j \in 1..Len(opQ[q]) :
                 /\ opQ[q][j].req.op = "Wr"
                 /\ opQ[q][j].req.adr = a
                 /\ opQ[q][j].req.val = v
        /\ opQ' = [opQ EXCEPT ![p][i].val = v, ![p][i].done = TRUE]
        /\ regFile' = [regFile EXCEPT ![p][r] = [state |-> "Free", val |-> v]]
  /\ UpdateOpOrder

\* Internal step: the system strengthens the ordering relation.
Internal ==
  /\ UNCHANGED <<regFile, opQ>>
  /\ UpdateOpOrder

Next ==
  \/ \E p \in Proc, req \in Request, r \in Reg : IssueRequest(p, req, r)
  \/ \E p \in Proc, r \in Reg : RespondToWr(p, r) \/ RespondToRd(p, r)
  \/ Internal

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness and liveness                                                   *)
(***************************************************************************)
Fairness ==
  /\ \A p \in Proc, r \in Reg : WF_vars(RespondToWr(p, r))
  /\ \A p \in Proc, r \in Reg : WF_vars(RespondToRd(p, r))
  /\ WF_vars(Internal /\ opOrder' # opOrder)

\* Every pending operation eventually receives a response.
ResponseLiveness ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].state = "Busy") ~> (regFile[p][r].state = "Free")

\* Ordering eventually becomes total on any two distinct operations.
OrderLiveness ==
  \A oi, oj \in OpIdUniverse :
     (oi \in OpIds /\ oj \in OpIds /\ oi # oj)
        ~> (<<oi, oj>> \in opOrder \/ <<oj, oi>> \in opOrder)

Liveness == ResponseLiveness /\ OrderLiveness

Spec == Init /\ [][Next]_vars /\ Fairness /\ Liveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
  /\ regFile \in [Proc -> [Reg -> RegContents]]
  /\ \A p \in Proc : opQ[p] \in Seq(OpRecord)
  /\ opOrder \subseteq (OpIds \X OpIds)

\* Primary correctness condition.
SerializabilityInv == Serializable(opQ, opOrder)

\* Each register holds at most one pending operation, and it is busy
\* exactly when it holds one.
RegisterExclusivity ==
  \A p \in Proc, r \in Reg :
     /\ Cardinality(PendingIdx(p, r)) <= 1
     /\ (regFile[p][r].state = "Busy") <=> (Cardinality(PendingIdx(p, r)) = 1)
     /\ \A i \in PendingIdx(p, r) : opQ[p][i].req = regFile[p][r].req

\* Every completed read returns initial memory or a value written to that address.
ReadValuesValid ==
  \A p \in Proc : \A i \in 1..Len(opQ[p]) :
     LET o == opQ[p][i] IN
     (o.req.op = "Rd" /\ o.done) =>
        \/ o.val = InitMem[o.req.adr]
        \/ \E q \in Proc : \E j \in 1..Len(opQ[q]) :
              /\ opQ[q][j].req.op = "Wr"
              /\ opQ[q][j].req.adr = o.req.adr
              /\ opQ[q][j].req.val = o.val

\* Pending reads have no value; completed reads do.
ReadValueConsistency ==
  \A p \in Proc : \A i \in 1..Len(opQ[p]) :
     opQ[p][i].req.op = "Rd" => (opQ[p][i].done <=> opQ[p][i].val # NoVal)

Invariants ==
  /\ TypeOK
  /\ SerializabilityInv
  /\ RegisterExclusivity
  /\ ReadValuesValid
  /\ ReadValueConsistency

THEOREM Spec => []Invariants
THEOREM Spec => Liveness
=============================================================================