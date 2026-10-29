---------------------------- MODULE MCInnerSequential ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          Reg,       \* set of register indices per processor
          Done,      \* value returned by a completed write (not in Val)
          MaxQLen    \* bound on operation queue length (model checking)

ASSUME Done \notin Val

VARIABLES regFile,   \* regFile[p][r] : register entry at processor p
          opQ,       \* opQ[p] : sequence of registers whose ops await execution
          mem        \* the (sequential) memory

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
(* Register file entries                                                    *)
-----------------------------------------------------------------------------
RegEntry == [op : {"Free", "Rd", "Wr", "Done"}, adr : Adr, val : Val \cup {Done}]

InitEntry == [op |-> "Free", adr |-> CHOOSE a \in Adr : TRUE,
              val |-> CHOOSE v \in Val : TRUE]

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegEntry]]
  /\ opQ \in [Proc -> Seq(Reg)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc : \A i \in 1..Len(opQ[p]) :
        regFile[p][opQ[p][i]].op \in {"Rd", "Wr"}

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> InitEntry]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

(* Processor p issues a read request into a free register r *)
ReqRd(p, r) ==
  /\ regFile[p][r].op = "Free"
  /\ \E a \in Adr :
       regFile' = [regFile EXCEPT ![p][r] =
                     [op |-> "Rd", adr |-> a, val |-> regFile[p][r].val]]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED mem

(* Processor p issues a write request into a free register r *)
ReqWr(p, r) ==
  /\ regFile[p][r].op = "Free"
  /\ \E a \in Adr, v \in Val :
       regFile' = [regFile EXCEPT ![p][r] = [op |-> "Wr", adr |-> a, val |-> v]]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, r)]
  /\ UNCHANGED mem

(* Execute the oldest pending operation of processor p on the memory *)
Do(p) ==
  /\ opQ[p] /= << >>
  /\ LET r == Head(opQ[p])
         e == regFile[p][r]
     IN  /\ IF e.op = "Rd"
              THEN /\ regFile' = [regFile EXCEPT ![p][r] =
                                    [op |-> "Done", adr |-> e.adr, val |-> mem[e.adr]]]
                   /\ UNCHANGED mem
              ELSE /\ mem' = [mem EXCEPT ![e.adr] = e.val]
                   /\ regFile' = [regFile EXCEPT ![p][r] =
                                    [op |-> "Done", adr |-> e.adr, val |-> Done]]
         /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]

(* Processor p consumes the response in register r, freeing it *)
Rsp(p, r) ==
  /\ regFile[p][r].op = "Done"
  /\ regFile' = [regFile EXCEPT ![p][r].op = "Free"]
  /\ UNCHANGED <<opQ, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg : ReqRd(p, r) \/ ReqWr(p, r) \/ Rsp(p, r)
  \/ \E p \in Proc : Do(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc : WF_vars(Do(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Rsp(p, r))

-----------------------------------------------------------------------------
(* Model-checking constraint and liveness property                          *)
-----------------------------------------------------------------------------
Constraint == \A p \in Proc : Len(opQ[p]) <= MaxQLen

AlwaysResponds ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op /= "Free") ~> (regFile[p][r].op = "Free")

=============================================================================