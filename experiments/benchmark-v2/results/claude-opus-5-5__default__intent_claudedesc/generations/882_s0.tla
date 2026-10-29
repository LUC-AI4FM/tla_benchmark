--------------------------- MODULE SequentialMemoryQueues ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val,    \* set of storable values
          Reg     \* set of register slots available to each processor

ASSUME Proc # {} /\ Adr # {} /\ Val # {} /\ Reg # {}

NoVal == CHOOSE v : v \notin Val
NoReg == CHOOSE r : r \notin Reg

InitMem == CHOOSE m \in [Adr -> Val] : TRUE

VARIABLES mem,       \* shared memory: Adr -> Val
          regFile,   \* regFile[p][r]: register interface for processor p
          opQ,       \* opQ[p]: internal queue of p's operations, in issue order
          issued,    \* issued[p]: number of operations issued by p (history)
          retired    \* retired[p]: number of operations retired for p (history)

vars == <<mem, regFile, opQ, issued, retired>>

-----------------------------------------------------------------------------
RegEntry ==
       [op : {"Free"}, adr : Adr \cup {NoVal}, val : Val \cup {NoVal}]
  \cup [op : {"Rd"},   adr : Adr, val : {NoVal}]
  \cup [op : {"Wr"},   adr : Adr, val : Val]

QEntry ==
  [op : {"Rd", "Wr"}, adr : Adr, val : Val \cup {NoVal},
   reg : Reg \cup {NoReg}, executed : BOOLEAN, responded : BOOLEAN]

TypeOK ==
  /\ mem \in [Adr -> Val]
  /\ regFile \in [Proc -> [Reg -> RegEntry]]
  /\ \A p \in Proc : opQ[p] \in Seq(QEntry)
  /\ issued \in [Proc -> Nat]
  /\ retired \in [Proc -> Nat]

-----------------------------------------------------------------------------
Init ==
  /\ mem = InitMem
  /\ regFile = [p \in Proc |-> [r \in Reg |-> [op |-> "Free", adr |-> NoVal, val |-> NoVal]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ issued = [p \in Proc |-> 0]
  /\ retired = [p \in Proc |-> 0]

\* Processor p issues a read or write request in free register r.
Req(p, r) ==
  /\ regFile[p][r].op = "Free"
  /\ \E a \in Adr :
       \/ /\ regFile' = [regFile EXCEPT ![p][r] = [op |-> "Rd", adr |-> a, val |-> NoVal]]
          /\ opQ' = [opQ EXCEPT ![p] = Append(@,
                       [op |-> "Rd", adr |-> a, val |-> NoVal, reg |-> r,
                        executed |-> FALSE, responded |-> FALSE])]
       \/ \E v \in Val :
          /\ regFile' = [regFile EXCEPT ![p][r] = [op |-> "Wr", adr |-> a, val |-> v]]
          /\ opQ' = [opQ EXCEPT ![p] = Append(@,
                       [op |-> "Wr", adr |-> a, val |-> v, reg |-> r,
                        executed |-> FALSE, responded |-> FALSE])]
  /\ issued' = [issued EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<mem, retired>>

\* Apply to memory the earliest not-yet-executed operation of processor p.
Execute(p) ==
  \E i \in 1..Len(opQ[p]) :
    /\ ~opQ[p][i].executed
    /\ \A j \in 1..(i-1) : opQ[p][j].executed
    /\ LET e == opQ[p][i] IN
         IF e.op = "Wr"
           THEN /\ mem' = [mem EXCEPT ![e.adr] = e.val]
                /\ opQ' = [opQ EXCEPT ![p][i].executed = TRUE]
           ELSE /\ opQ' = [opQ EXCEPT ![p][i].executed = TRUE,
                                      ![p][i].val = mem[e.adr]]
                /\ UNCHANGED mem
    /\ UNCHANGED <<regFile, issued, retired>>

\* Respond to the pending operation in register r of processor p (any order).
\* Reads may respond only after they have been executed; writes may be acked early.
Rsp(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ \E i \in 1..Len(opQ[p]) :
       /\ opQ[p][i].reg = r
       /\ opQ[p][i].op = "Wr" \/ opQ[p][i].executed
       /\ regFile' = [regFile EXCEPT ![p][r] =
                        [op  |-> "Free",
                         adr |-> regFile[p][r].adr,
                         val |-> IF opQ[p][i].op = "Rd" THEN opQ[p][i].val ELSE NoVal]]
       /\ opQ' = [opQ EXCEPT ![p][i].reg = NoReg, ![p][i].responded = TRUE]
  /\ UNCHANGED <<mem, issued, retired>>

\* Retire a completed (executed and responded) operation from the head of the queue.
Retire(p) ==
  /\ Len(opQ[p]) > 0
  /\ Head(opQ[p]).executed
  /\ Head(opQ[p]).responded
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ retired' = [retired EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<mem, regFile, issued>>

Next ==
  \/ \E p \in Proc, r \in Reg : Req(p, r) \/ Rsp(p, r)
  \/ \E p \in Proc : Execute(p) \/ Retire(p)

Fairness ==
  /\ \A p \in Proc : WF_vars(Execute(p))
  /\ \A p \in Proc : WF_vars(Retire(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Rsp(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants

\* Each pending register has exactly one matching queue entry; free registers have none.
DataIntegrity ==
  \A p \in Proc, r \in Reg :
    LET idx == {i \in 1..Len(opQ[p]) : opQ[p][i].reg = r} IN
      IF regFile[p][r].op = "Free"
        THEN idx = {}
        ELSE /\ Cardinality(idx) = 1
             /\ \A i \in idx : /\ opQ[p][i].op = regFile[p][r].op
                               /\ opQ[p][i].adr = regFile[p][r].adr
                               /\ ~opQ[p][i].responded

\* Operations take effect in issue order: executed entries form a prefix of the queue.
ExecutedInOrder ==
  \A p \in Proc : \A i, j \in 1..Len(opQ[p]) :
    (i < j /\ opQ[p][j].executed) => opQ[p][i].executed

\* Responded entries no longer occupy a register.
RespondedConsistent ==
  \A p \in Proc : \A i \in 1..Len(opQ[p]) :
    opQ[p][i].responded <=> (opQ[p][i].reg = NoReg)

\* Sequential consistency per processor (action properties):
\* (a) A read, when applied, takes the current memory value at that point,
\*     after all earlier operations of the same processor have taken effect.
ReadAppliedCorrectly ==
  \A p \in Proc : \A i \in 1..Len(opQ[p]) :
    ( /\ ~opQ[p][i].executed
      /\ i \in 1..Len(opQ'[p])
      /\ opQ'[p][i].executed
      /\ opQ[p][i].op = "Rd" )
    => /\ opQ'[p][i].val = mem[opQ[p][i].adr]
       /\ \A j \in 1..(i-1) : opQ[p][j].executed

\* (b) A completed read returns exactly the value read at its execution point.
ReadReturnsAppliedValue ==
  \A p \in Proc, r \in Reg :
    (regFile[p][r].op = "Rd" /\ regFile'[p][r].op = "Free")
    => \E i \in 1..Len(opQ[p]) :
         /\ opQ[p][i].reg = r
         /\ opQ[p][i].executed
         /\ regFile'[p][r].val = opQ[p][i].val

SequentialConsistency ==
  [][ReadAppliedCorrectly /\ ReadReturnsAppliedValue]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* Every issued operation eventually receives a response.
EventualResponse ==
  \A p \in Proc, r \in Reg :
    (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

\* Every issued operation is eventually executed, responded to, and retired.
EventualRetirement ==
  \A p \in Proc, n \in Nat :
    (issued[p] >= n) ~> (retired[p] >= n)

EventualCompletion == EventualResponse /\ EventualRetirement

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ DataIntegrity /\ ExecutedInOrder /\ RespondedConsistent)
THEOREM Spec => SequentialConsistency
THEOREM Spec => EventualCompletion
=============================================================================