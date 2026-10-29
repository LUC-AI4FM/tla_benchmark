------------------------------ MODULE SerialMemory ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          Reg,       \* set of registers per process
          InitMem    \* initial memory contents

ASSUME InitMem \in [Adr -> Val]

VARIABLES regFile,   \* regFile[p][r] : contents of register r of process p
          opQ,       \* opQ[p] : sequence of operations issued by process p
          opOrder    \* the ordering relation established so far on operations

vars == <<regFile, opQ, opOrder>>

-----------------------------------------------------------------------------
(* Register contents                                                       *)
-----------------------------------------------------------------------------
DefaultAdr == CHOOSE a \in Adr : TRUE
DefaultVal == CHOOSE v \in Val : TRUE

RdRequest  == {[op |-> "Rd", adr |-> a, val |-> DefaultVal] : a \in Adr}
WrRequest  == [op : {"Wr"}, adr : Adr, val : Val]
IssuableRequest == RdRequest \cup WrRequest

Request    == [op : {"Rd", "Wr"}, adr : Adr, val : Val]
FreeRegValue == [op : {"Free"}, adr : Adr, val : Val]
RegValue   == Request \cup FreeRegValue

FreeReg == [op |-> "Free", adr |-> DefaultAdr, val |-> DefaultVal]

RegFileTypeInvariant == regFile \in [Proc -> [Reg -> RegValue]]

-----------------------------------------------------------------------------
(* Operation identifiers and the operation queue                           *)
-----------------------------------------------------------------------------
opId == [proc : Proc, idx : Nat \ {0}]

opIdQ(oi) == opQ[oi.proc][oi.idx]

\* Fictitious "write" that produced the initial memory contents
InitWr == CHOOSE v : v \notin [proc : Proc, idx : Nat]

\* Value of the reg field of a completed operation
Done == CHOOSE v : v \notin Reg

opVal == [req : Request, reg : Reg \cup {Done}, source : opId \cup {InitWr}]

DataInvariant ==
  /\ RegFileTypeInvariant
  /\ opQ \in [Proc -> Seq(opVal)]
  /\ opOrder \subseteq (opId \X opId)

\* The set of operations issued so far
CurOps == {[proc |-> p, idx |-> i] : p \in Proc, i \in 1..Len(opQ[p])}

IsWrTo(oi, a) == /\ opIdQ(oi).req.op = "Wr"
                 /\ opIdQ(oi).req.adr = a

-----------------------------------------------------------------------------
(* Serializability                                                         *)
-----------------------------------------------------------------------------
Perms(S) == {f \in [1..Cardinality(S) -> S] :
               \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]}

Pos(s, o) == CHOOSE i \in DOMAIN s : s[i] = o

Serializable ==
  LET ops == CurOps
  IN \E s \in Perms(ops) :
       LET Before(a, b) == Pos(s, a) < Pos(s, b)
       IN  /\ \A pr \in opOrder : Before(pr[1], pr[2])
           /\ \A o1, o2 \in ops :
                 (o1.proc = o2.proc /\ o1.idx < o2.idx) => Before(o1, o2)
           /\ \A rd \in ops :
                 LET e   == opIdQ(rd)
                     adr == e.req.adr
                 IN  (e.req.op = "Rd" /\ e.reg = Done) =>
                       IF e.source = InitWr
                         THEN /\ e.req.val = InitMem[adr]
                              /\ \A w \in ops : IsWrTo(w, adr) => ~Before(w, rd)
                         ELSE /\ e.source \in ops
                              /\ IsWrTo(e.source, adr)
                              /\ opIdQ(e.source).req.val = e.req.val
                              /\ Before(e.source, rd)
                              /\ \A w \in ops :
                                   IsWrTo(w, adr) =>
                                      ~(Before(e.source, w) /\ Before(w, rd))

-----------------------------------------------------------------------------
(* Initial state and actions                                               *)
-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

PendIdx(p, r) == CHOOSE i \in 1..Len(opQ[p]) : opQ[p][i].reg = r

IssueRequest(p, r, req) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r, source |-> InitWr])]
  /\ UNCHANGED opOrder

RespondWr(p, r) ==
  /\ regFile[p][r].op = "Wr"
  /\ LET i == PendIdx(p, r)
     IN  opQ' = [opQ EXCEPT ![p][i].reg = Done]
  /\ regFile' = [regFile EXCEPT ![p][r].op = "Free"]
  /\ UNCHANGED opOrder

RespondRd(p, r) ==
  /\ regFile[p][r].op = "Rd"
  /\ LET i   == PendIdx(p, r)
         adr == regFile[p][r].adr
         goodSource == {InitWr} \cup {w \in CurOps : IsWrTo(w, adr)}
     IN  \E src \in goodSource :
           LET v == IF src = InitWr THEN InitMem[adr]
                                    ELSE opIdQ(src).req.val
           IN  /\ opQ' = [opQ EXCEPT ![p][i] =
                            [req    |-> [@.req EXCEPT !.val = v],
                             reg    |-> Done,
                             source |-> src]]
               /\ regFile' = [regFile EXCEPT ![p][r] =
                                [@ EXCEPT !.val = v, !.op = "Free"]]
               /\ UNCHANGED opOrder
               /\ Serializable'

ExtendOrder ==
  /\ \E o1, o2 \in CurOps :
        /\ o1 # o2
        /\ <<o1, o2>> \notin opOrder
        /\ <<o2, o1>> \notin opOrder
        /\ opOrder' = opOrder \cup {<<o1, o2>>}
        /\ Serializable'
  /\ UNCHANGED <<regFile, opQ>>

Next ==
  \/ \E p \in Proc, r \in Reg :
        \/ \E req \in IssuableRequest : IssueRequest(p, r, req)
        \/ RespondWr(p, r)
        \/ RespondRd(p, r)
  \/ ExtendOrder

Fairness ==
  /\ \A p \in Proc, r \in Reg : WF_vars(RespondWr(p, r) \/ RespondRd(p, r))
  /\ WF_vars(ExtendOrder)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------
RegisterExclusivity ==
  \A p \in Proc, r \in Reg :
     Cardinality({i \in 1..Len(opQ[p]) : opQ[p][i].reg = r}) <=
        (IF regFile[p][r].op = "Free" THEN 0 ELSE 1)

SerialInvariant == Serializable

EventualResponse ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

EventualOrdering ==
  \A p1, p2 \in Proc, i1, i2 \in 1..3 :
     LET o1 == [proc |-> p1, idx |-> i1]
         o2 == [proc |-> p2, idx |-> i2]
     IN  (o1 \in CurOps /\ o2 \in CurOps /\ o1 # o2) ~>
            (<<o1, o2>> \in opOrder \/ <<o2, o1>> \in opOrder)
=============================================================================