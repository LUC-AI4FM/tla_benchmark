--------------------------- MODULE MCInnerSerial ---------------------------
(***************************************************************************)
(* Model-checking wrapper for the InnerSerial memory specification.        *)
(* The InnerSerial memory is given inline so the module is self-contained. *)
(* MCNat bounds the natural numbers, qConstraint limits each process's     *)
(* operation queue to MaxQLen, MCInitMem is an arbitrary initial memory    *)
(* that can be substituted for InitMem, and AlwaysResponds is the          *)
(* liveness property to check.                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          Reg,       \* set of registers per processor
          InitMem,   \* initial contents of memory
          MaxQLen    \* bound on the length of each operation queue

ASSUME /\ InitMem \in [Adr -> Val]
       /\ MaxQLen \in Nat

VARIABLES regFile,   \* regFile[p][r] : register contents (or Free)
          opQ,       \* opQ[p] : sequence of operations issued by p
          opOrder,   \* serial order of executed operations
          mem        \* current serial memory contents

vars == <<regFile, opQ, opOrder, mem>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Definitions of the model-checking wrapper                               *)
(***************************************************************************)
MCNat == 0 .. MaxQLen

MCInitMem == CHOOSE m \in [Adr -> Val] : TRUE

-----------------------------------------------------------------------------
(***************************************************************************)
(* Data types                                                              *)
(***************************************************************************)
Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

Reply == Val \cup {NoVal}

RegEntry == [req : Request, reply : Reply, done : BOOLEAN]

Free == CHOOSE v : v \notin RegEntry

OpState == {"issued", "executed", "done"}

OpEntry == [req : Request, reg : Reg, state : OpState, reply : Reply]

OpIdSet == [proc : Proc, idx : Nat \ {0}]

(* The set of identifiers of all operations currently in some opQ[p]. *)
opId == UNION { { [proc |-> p, idx |-> i] : i \in DOMAIN opQ[p] } : p \in Proc }

(* State constraint: bound the length of each queue for TLC. *)
qConstraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state and actions                                               *)
(***************************************************************************)
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> Free]]
  /\ opQ     = [p \in Proc |-> << >>]
  /\ opOrder = << >>
  /\ mem     = InitMem

(* Processor p issues request req using free register r. *)
Issue(p, r, req) ==
  /\ regFile[p][r] = Free
  /\ regFile' = [regFile EXCEPT ![p][r] =
                   [req |-> req, reply |-> NoVal, done |-> FALSE]]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r,
                          state |-> "issued", reply |-> NoVal])]
  /\ UNCHANGED <<opOrder, mem>>

(* The i-th operation of p is executed atomically on the serial memory, *)
(* respecting p's program order.                                         *)
Execute(p, i) ==
  /\ i \in DOMAIN opQ[p]
  /\ opQ[p][i].state = "issued"
  /\ \A j \in 1 .. (i - 1) : opQ[p][j].state # "issued"
  /\ LET req == opQ[p][i].req
         rep == IF req.op = "Rd" THEN mem[req.adr] ELSE NoVal
     IN  /\ mem' = IF req.op = "Wr"
                     THEN [mem EXCEPT ![req.adr] = req.val]
                     ELSE mem
         /\ opQ' = [opQ EXCEPT ![p][i].state = "executed",
                               ![p][i].reply = rep]
  /\ opOrder' = Append(opOrder, [proc |-> p, idx |-> i])
  /\ UNCHANGED regFile

(* The reply of an executed operation is placed in its register. *)
Respond(p, i) ==
  /\ i \in DOMAIN opQ[p]
  /\ opQ[p][i].state = "executed"
  /\ LET r == opQ[p][i].reg
     IN  regFile' = [regFile EXCEPT ![p][r].reply = opQ[p][i].reply,
                                    ![p][r].done  = TRUE]
  /\ opQ' = [opQ EXCEPT ![p][i].state = "done"]
  /\ UNCHANGED <<opOrder, mem>>

(* Processor p consumes the reply, freeing register r. *)
Consume(p, r) ==
  /\ regFile[p][r] # Free
  /\ regFile[p][r].done
  /\ regFile' = [regFile EXCEPT ![p][r] = Free]
  /\ UNCHANGED <<opQ, opOrder, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
  \/ \E p \in Proc, i \in MCNat \ {0} : Execute(p, i)
  \/ \E p \in Proc, i \in MCNat \ {0} : Respond(p, i)
  \/ \E p \in Proc, r \in Reg : Consume(p, r)

Fairness ==
  /\ \A p \in Proc, i \in MCNat \ {0} : WF_vars(Execute(p, i))
  /\ \A p \in Proc, i \in MCNat \ {0} : WF_vars(Respond(p, i))
  /\ \A p \in Proc, r \in Reg : WF_vars(Consume(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
  /\ regFile \in [Proc -> [Reg -> RegEntry \cup {Free}]]
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ opOrder \in Seq(OpIdSet)
  /\ mem \in [Adr -> Val]

(* Every operation in opOrder is a known, executed operation, and none *)
(* appears twice.                                                       *)
OrderOK ==
  /\ \A k \in DOMAIN opOrder :
        /\ opOrder[k] \in opId
        /\ opQ[opOrder[k].proc][opOrder[k].idx].state # "issued"
  /\ \A k1, k2 \in DOMAIN opOrder : (opOrder[k1] = opOrder[k2]) => (k1 = k2)

(* Every non-issued operation appears in opOrder. *)
ExecutedInOrder ==
  \A p \in Proc : \A i \in DOMAIN opQ[p] :
     (opQ[p][i].state # "issued") <=>
        (\E k \in DOMAIN opOrder : opOrder[k] = [proc |-> p, idx |-> i])

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness property                                                       *)
(***************************************************************************)
AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
        (regFile[p][r] # Free) ~> (regFile[p][r] = Free)
  /\ \A p \in Proc, i \in MCNat \ {0} :
        ([proc |-> p, idx |-> i] \in opId)
           ~> (/\ i \in DOMAIN opQ[p]
               /\ opQ[p][i].state = "done")

THEOREM Spec => [](TypeOK /\ OrderOK /\ ExecutedInOrder)
=============================================================================