---------------------------- MODULE MCInnerSerial ----------------------------
(***************************************************************************)
(* Model-checking harness for the InnerSerial specification.               *)
(* Processors issue memory requests through registers. Each request is      *)
(* appended to the processor's operation queue. Requests are executed       *)
(* one at a time against a single shared memory, which makes the execution  *)
(* serial. A processor executes its own requests in program order. A        *)
(* completed request is answered in its register. The operation is then     *)
(* marked "Done" and later removed from the queue.                          *)
(*                                                                          *)
(* Suggested TLC configuration (MCInnerSerial.cfg):                          *)
(*   CONSTANTS  Reg = {r1}  Adr = {a1}  Val = {v1, v2}                       *)
(*              Proc = {p1, p2}  MaxQLen = 1                                 *)
(*   CONSTRAINT Constraint                                                   *)
(*   SPECIFICATION Spec                                                      *)
(*   INVARIANT  DataInvariant                                                *)
(*   PROPERTY   AlwaysResponds                                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val, Reg, MaxQLen

ASSUME MaxQLen \in Nat

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

---------------------------------------------------------------------------
(* Model-checking overrides *)

MCNat == 0..MaxQLen

MCInitMem == CHOOSE m \in [Adr -> Val] : TRUE

Constraint == \A p \in Proc : Len(opQ[p]) <= MaxQLen

---------------------------------------------------------------------------
(* Data types *)

RegValue == [op : {"Free", "Rd", "Wr"}, adr : Adr, val : Val]

Request == [op : {"Rd", "Wr"}, adr : Adr, val : Val]

NoResult == "none"

OpEntry == [req    : Request,
            reg    : Reg \cup {"Done"},
            exec   : BOOLEAN,
            result : Val \cup {NoResult}]

opId(q) == {[proc |-> p, idx |-> i] : p \in Proc, i \in DOMAIN q[p]}

---------------------------------------------------------------------------
Init ==
  /\ regFile \in [Proc -> [Reg -> [op : {"Free"}, adr : Adr, val : Val]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem = MCInitMem

(* Processor p issues request req in a free register r. *)
IssueRequest(p, r, req) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r,
                          exec |-> FALSE, result |-> NoResult])]
  /\ UNCHANGED mem

(* Execute the oldest unexecuted op of p against memory (serialization). *)
Execute(p) ==
  \E i \in DOMAIN opQ[p] :
     /\ ~opQ[p][i].exec
     /\ \A j \in 1..(i-1) : opQ[p][j].exec
     /\ LET e == opQ[p][i]
        IN  IF e.req.op = "Wr"
              THEN /\ mem' = [mem EXCEPT ![e.req.adr] = e.req.val]
                   /\ opQ' = [opQ EXCEPT ![p][i].exec = TRUE]
              ELSE /\ opQ' = [opQ EXCEPT ![p][i].exec = TRUE,
                                         ![p][i].result = mem[e.req.adr]]
                   /\ UNCHANGED mem
     /\ UNCHANGED regFile

(* Respond to the executed request held in register r of processor p. *)
Respond(p, r) ==
  \E i \in DOMAIN opQ[p] :
     /\ opQ[p][i].reg = r
     /\ opQ[p][i].exec
     /\ regFile[p][r].op # "Free"
     /\ regFile' = [regFile EXCEPT ![p][r] =
                      [op  |-> "Free",
                       adr |-> @.adr,
                       val |-> IF opQ[p][i].req.op = "Rd"
                                 THEN opQ[p][i].result
                                 ELSE @.val]]
     /\ opQ' = [opQ EXCEPT ![p][i].reg = "Done"]
     /\ UNCHANGED mem

(* Remove a completed op from the head of p's queue. *)
RemoveOp(p) ==
  /\ Len(opQ[p]) > 0
  /\ Head(opQ[p]).reg = "Done"
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<regFile, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : IssueRequest(p, r, req)
  \/ \E p \in Proc : Execute(p)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)
  \/ \E p \in Proc : RemoveOp(p)

Fairness ==
  /\ \A p \in Proc : WF_vars(Execute(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety *)

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegValue]]
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc :
       /\ \A i \in DOMAIN opQ[p] :
            /\ opQ[p][i].reg = "Done" => opQ[p][i].exec
            /\ (opQ[p][i].exec /\ opQ[p][i].req.op = "Rd")
                  => opQ[p][i].result \in Val
            /\ opQ[p][i].reg \in Reg =>
                  regFile[p][opQ[p][i].reg] = opQ[p][i].req
            /\ opQ[p][i].exec => \A j \in 1..(i-1) : opQ[p][j].exec
       /\ \A r \in Reg :
            (regFile[p][r].op # "Free") <=>
               (Cardinality({i \in DOMAIN opQ[p] : opQ[p][i].reg = r}) = 1)

---------------------------------------------------------------------------
(* Liveness *)

AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
        (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in [proc : Proc, idx : MCNat] :
        (oi \in opId(opQ))
           ~> ((oi \notin opId(opQ)) \/ (opQ[oi.proc][oi.idx].reg = "Done"))

THEOREM Spec => []DataInvariant
THEOREM Spec => AlwaysResponds
=============================================================================