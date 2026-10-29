---------------------------- MODULE InnerSequential ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val, Reg

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------

Done  == CHOOSE v : v \notin Reg
NoRes == CHOOSE v : v \notin Val
Ack   == "Ack"

RdRequest == [op : {"Rd"}, adr : Adr]
WrRequest == [op : {"Wr"}, adr : Adr, val : Val]
Request   == RdRequest \cup WrRequest

FreeRegValue == [op : {"Free"}, val : Val \cup {Ack}]
RegValue     == Request \cup FreeRegValue

IsFree(p, r) == regFile[p][r].op = "Free"

QEntry == [req : Request, reg : Reg \cup {Done}, exec : BOOLEAN, res : Val \cup {NoRes}]

RegFileTypeInvariant == regFile \in [Proc -> [Reg -> RegValue]]

DataInvariant ==
  /\ RegFileTypeInvariant
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        Cardinality({i \in DOMAIN opQ[p] : opQ[p][i].reg = r})
           = IF IsFree(p, r) THEN 0 ELSE 1
  /\ \A p \in Proc, r \in Reg :
        \A i \in DOMAIN opQ[p] :
           opQ[p][i].reg = r => opQ[p][i].req = regFile[p][r]
  /\ \A p \in Proc : \A i \in DOMAIN opQ[p] :
        opQ[p][i].exec => \A j \in 1..(i-1) : opQ[p][j].exec

-----------------------------------------------------------------------------

Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> [op |-> "Free", val |-> Ack]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

IssueRequest(p, req, r) ==
  /\ IsFree(p, r)
  /\ Len(opQ[p]) < Cardinality(Reg)
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r,
                                          exec |-> FALSE, res |-> NoRes])]
  /\ UNCHANGED mem

Execute(p) ==
  /\ \E i \in DOMAIN opQ[p] :
       /\ ~opQ[p][i].exec
       /\ \A j \in 1..(i-1) : opQ[p][j].exec
       /\ LET e == opQ[p][i] IN
            IF e.req.op = "Wr"
              THEN /\ mem' = [mem EXCEPT ![e.req.adr] = e.req.val]
                   /\ opQ' = [opQ EXCEPT ![p][i].exec = TRUE]
              ELSE /\ opQ' = [opQ EXCEPT ![p][i].exec = TRUE,
                                         ![p][i].res  = mem[e.req.adr]]
                   /\ UNCHANGED mem
  /\ UNCHANGED regFile

RespondToRd(p, r) ==
  /\ regFile[p][r].op = "Rd"
  /\ \E i \in DOMAIN opQ[p] :
       /\ opQ[p][i].reg = r
       /\ opQ[p][i].exec
       /\ regFile' = [regFile EXCEPT ![p][r] = [op |-> "Free", val |-> opQ[p][i].res]]
       /\ opQ' = [opQ EXCEPT ![p][i].reg = Done]
  /\ UNCHANGED mem

RespondToWr(p, r) ==
  /\ regFile[p][r].op = "Wr"
  /\ \E i \in DOMAIN opQ[p] :
       /\ opQ[p][i].reg = r
       /\ regFile' = [regFile EXCEPT ![p][r] = [op |-> "Free", val |-> Ack]]
       /\ opQ' = [opQ EXCEPT ![p][i].reg = Done]
  /\ UNCHANGED mem

Respond(p, r) == RespondToRd(p, r) \/ RespondToWr(p, r)

RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

Retire(p) ==
  /\ \E i \in DOMAIN opQ[p] :
       /\ opQ[p][i].exec
       /\ opQ[p][i].reg = Done
       /\ opQ' = [opQ EXCEPT ![p] = RemoveAt(@, i)]
  /\ UNCHANGED <<regFile, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : IssueRequest(p, req, r)
  \/ \E p \in Proc : Execute(p)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)
  \/ \E p \in Proc : Retire(p)

Fairness ==
  \A p \in Proc :
     /\ WF_vars(Execute(p))
     /\ WF_vars(Retire(p))
     /\ \A r \in Reg : WF_vars(Respond(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

ReadsConsistent ==
  \A p \in Proc, r \in Reg :
     RespondToRd(p, r) =>
        \E i \in DOMAIN opQ[p] :
           /\ opQ[p][i].reg = r
           /\ regFile'[p][r].val = opQ[p][i].res

SequentialConsistency == [][ReadsConsistent]_vars

Liveness ==
  /\ \A p \in Proc, r \in Reg : (~IsFree(p, r)) ~> IsFree(p, r)
  /\ \A p \in Proc : []<>(\A i \in DOMAIN opQ[p] : opQ[p][i].reg # Done)

THEOREM Spec => []DataInvariant
=============================================================================