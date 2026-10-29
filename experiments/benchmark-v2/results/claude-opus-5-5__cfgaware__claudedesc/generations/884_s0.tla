------------------------------ MODULE MCInnerSequential ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Reg, Adr, Val, Proc, Done, MaxQLen

ASSUME Done \notin Val
ASSUME MaxQLen \in Nat

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

RegBusy == [req : Request, val : Val \cup {Done}, status : {"Issued", "Executed"}]

RegState == {"Free"} \cup RegBusy

QEntry == [req : Request, reg : Reg]

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegState]]
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc : \A i \in 1..Len(opQ[p]) :
        /\ regFile[p][opQ[p][i].reg] # "Free"
        /\ regFile[p][opQ[p][i].reg].status = "Issued"
        /\ regFile[p][opQ[p][i].reg].req = opQ[p][i].req
  /\ \A p \in Proc : \A i, j \in 1..Len(opQ[p]) :
        (i # j) => (opQ[p][i].reg # opQ[p][j].reg)
  /\ \A p \in Proc : \A r \in Reg :
        (regFile[p][r] # "Free" /\ regFile[p][r].status = "Issued")
          => \E i \in 1..Len(opQ[p]) : opQ[p][i].reg = r

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> "Free"]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

Issue(p, r, req) ==
  /\ regFile[p][r] = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] =
                   [req |-> req, val |-> Done, status |-> "Issued"]]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED mem

Execute(p) ==
  /\ opQ[p] # << >>
  /\ LET e   == Head(opQ[p])
         req == e.req
     IN  /\ IF req.op = "Rd"
               THEN /\ regFile' = [regFile EXCEPT ![p][e.reg] =
                                     [req |-> req, val |-> mem[req.adr],
                                      status |-> "Executed"]]
                    /\ UNCHANGED mem
               ELSE /\ mem' = [mem EXCEPT ![req.adr] = req.val]
                    /\ regFile' = [regFile EXCEPT ![p][e.reg] =
                                     [req |-> req, val |-> Done,
                                      status |-> "Executed"]]
         /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]

Respond(p, r) ==
  /\ regFile[p][r] # "Free"
  /\ regFile[p][r].status = "Executed"
  /\ regFile' = [regFile EXCEPT ![p][r] = "Free"]
  /\ UNCHANGED <<opQ, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
  \/ \E p \in Proc : Execute(p)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc : WF_vars(Execute(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))

-----------------------------------------------------------------------------
Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

AlwaysResponds ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r] # "Free") ~> (regFile[p][r] = "Free")

=============================================================================