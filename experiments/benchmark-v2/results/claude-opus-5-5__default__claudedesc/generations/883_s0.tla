---------------------------- MODULE SerialMemory ----------------------------
(***************************************************************************)
(* A serializable memory for a multiprocessor with a register-based        *)
(* interface. The register interface (normally module RegisterInterface)   *)
(* is inlined here so that the module is self-contained.                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Register interface                                                      *)
(***************************************************************************)
CONSTANTS Adr, Val, Proc, Reg

VARIABLE regFile

RdRequest  == [adr : Adr, val : Val, op : {"Rd"}]
WrRequest  == [adr : Adr, val : Val, op : {"Wr"}]
Request    == RdRequest \cup WrRequest

\* A free register holds the result of its last response (if any).
FreeRegValues == [adr : Adr, val : Val, op : {"Free"}]

RegFileTypeInvariant ==
    regFile \in [Proc -> [Reg -> Request \cup FreeRegValues]]

(***************************************************************************)
(* Serial memory                                                           *)
(***************************************************************************)
CONSTANT InitMem
ASSUME InitMem \in [Adr -> Val]

VARIABLES opQ, opOrder

vars == <<regFile, opQ, opOrder>>

Done == CHOOSE v : v \notin Reg

\* The set of identifiers of operations currently in the queues.
opId == UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc }

\* The queue entry of an operation identifier.
opIdQ(oi) == opQ[oi.proc][oi.idx]

\* Fictitious "write" that produced the initial memory contents.
InitWr == CHOOSE v : v \notin [proc : Proc, idx : Nat]

\* The valid write sources for a read operation oi.
goodSource(oi) ==
    {InitWr} \cup
    { o \in opId : /\ opIdQ(o).req.op = "Wr"
                   /\ opIdQ(o).req.adr = opIdQ(oi).req.adr }

\* Value obtained from source src at address a.
SourceVal(src, a) == IF src = InitWr THEN InitMem[a] ELSE opIdQ(src).req.val

-----------------------------------------------------------------------------
DataInvariant ==
  /\ RegFileTypeInvariant
  /\ opQ \in [Proc -> Seq(     [req : Request,   reg : Reg]
                          \cup [req : WrRequest, reg : {Done}]
                          \cup [req : RdRequest, reg : {Done},
                                source : opId \cup {InitWr}])]
  /\ opOrder \subseteq (opId \X opId)
  /\ \A p \in Proc, r \in Reg :
       /\ (regFile[p][r].op # "Free")
             <=> (\E i \in DOMAIN opQ[p] : opQ[p][i].reg = r)
       /\ \A i, j \in DOMAIN opQ[p] :
             (opQ[p][i].reg = r /\ opQ[p][j].reg = r) => (i = j)
       /\ \A i \in DOMAIN opQ[p] :
             (opQ[p][i].reg = r) => (regFile[p][r] = opQ[p][i].req)
  /\ \A oi \in opId :
       (opIdQ(oi).reg = Done /\ opIdQ(oi).req.op = "Rd")
          => opIdQ(oi).source \in goodSource(oi)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Serializability                                                         *)
(***************************************************************************)
totalOpOrder ==
  { R \in SUBSET (opId \X opId) :
      /\ \A oi, oj \in opId :
            (oi = oj) \/ (<<oi, oj>> \in R) \/ (<<oj, oi>> \in R)
      /\ \A oi, oj, ok \in opId :
            (<<oi, oj>> \in R /\ <<oj, ok>> \in R) => (<<oi, ok>> \in R)
      /\ \A oi \in opId : <<oi, oi>> \notin R }

Serializable ==
  \E R \in totalOpOrder :
    /\ opOrder \subseteq R
    /\ \A oi, oj \in opId :
          (oi.proc = oj.proc /\ oi.idx < oj.idx) => (<<oi, oj>> \in R)
    /\ \A oi \in opId :
          (opIdQ(oi).reg = Done /\ opIdQ(oi).req.op = "Rd") =>
             LET src == opIdQ(oi).source
             IN  /\ (src # InitWr) => (<<src, oi>> \in R)
                 /\ ~ \E oj \in goodSource(oi) \ {InitWr} :
                        /\ oj # src
                        /\ (src = InitWr) \/ (<<src, oj>> \in R)
                        /\ <<oj, oi>> \in R

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Init == /\ regFile \in [Proc -> [Reg -> FreeRegValues]]
        /\ opQ = [p \in Proc |-> << >>]
        /\ opOrder = {}

UpdateOpOrder(A) ==
  /\ A
  /\ opOrder' \in SUBSET (opId' \X opId')
  /\ opOrder \subseteq opOrder'
  /\ Serializable'

IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg].op = "Free"
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]

RespondToWr(proc, reg, idx) ==
  /\ idx \in DOMAIN opQ[proc]
  /\ opQ[proc][idx].reg = reg
  /\ opQ[proc][idx].req.op = "Wr"
  /\ regFile' = [regFile EXCEPT ![proc][reg].op = "Free"]
  /\ opQ' = [opQ EXCEPT ![proc][idx] = [req |-> @.req, reg |-> Done]]

RespondToRd(proc, reg, idx) ==
  /\ idx \in DOMAIN opQ[proc]
  /\ opQ[proc][idx].reg = reg
  /\ opQ[proc][idx].req.op = "Rd"
  /\ \E src \in goodSource([proc |-> proc, idx |-> idx]) :
       LET a == opQ[proc][idx].req.adr
       IN  /\ regFile' = [regFile EXCEPT ![proc][reg] =
                            [adr |-> a, val |-> SourceVal(src, a), op |-> "Free"]]
           /\ opQ' = [opQ EXCEPT ![proc][idx] =
                         [req |-> @.req, reg |-> Done, source |-> src]]

Respond(proc, reg, idx) ==
  \/ RespondToWr(proc, reg, idx)
  \/ RespondToRd(proc, reg, idx)

Internal == UNCHANGED <<regFile, opQ>>

Next ==
  \/ \E proc \in Proc, req \in Request, reg \in Reg :
        UpdateOpOrder(IssueRequest(proc, req, reg))
  \/ \E proc \in Proc, reg \in Reg :
        \E idx \in DOMAIN opQ[proc] : UpdateOpOrder(Respond(proc, reg, idx))
  \/ UpdateOpOrder(Internal)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness                                                                *)
(***************************************************************************)
Liveness ==
  /\ \A proc \in Proc, reg \in Reg :
        WF_vars(\E idx \in DOMAIN opQ[proc] :
                   UpdateOpOrder(Respond(proc, reg, idx)))
  /\ \A oi, oj \in [proc : Proc, idx : Nat] :
        WF_vars(/\ oi # oj
                /\ {oi, oj} \subseteq opId
                /\ <<oi, oj>> \notin opOrder
                /\ <<oj, oi>> \notin opOrder
                /\ UpdateOpOrder(/\ Internal
                                 /\ opOrder' \cap {<<oi, oj>>, <<oj, oi>>} # {}))

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
THEOREM Spec => [](DataInvariant /\ Serializable)
=============================================================================