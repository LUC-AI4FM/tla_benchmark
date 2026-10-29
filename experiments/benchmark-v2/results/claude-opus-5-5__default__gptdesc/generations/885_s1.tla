--------------------------- MODULE MCInnerSerial ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val, Reg, MaxQLen

ASSUME MaxQLen \in Nat

MCNat == 0..2

MCInitMem == CHOOSE m \in [Adr -> Val] : TRUE

InitMem == MCInitMem

NoVal == CHOOSE v : v \notin Val

DefaultAdr == CHOOSE a \in Adr : TRUE

Request == [op : {"Rd", "Wr"}, adr : Adr, val : Val \cup {NoVal}]

RegValue == [op : {"Free", "Rd", "Wr"}, adr : Adr, val : Val \cup {NoVal}]

QEntry == [req : Request, reg : Reg, done : BOOLEAN,
           resp : BOOLEAN, val : Val \cup {NoVal}]

OpIdSet == [proc : Proc, idx : MCNat]

VARIABLES regFile, opQ, opOrder, mem

vars == <<regFile, opQ, opOrder, mem>>

opId == { [proc |-> p, idx |-> i] : p \in Proc, i \in DOMAIN opQ[p] }

CompletedOps ==
  { [proc |-> p, idx |-> i] : p \in Proc,
      i \in { j \in DOMAIN opQ[p] : opQ[p][j].done /\ opQ[p][j].resp } }

TypeOK ==
  /\ regFile \in [Proc -> [Reg -> RegValue]]
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ opOrder \in Seq([proc : Proc, idx : Nat])
  /\ mem \in [Adr -> Val]

Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |->
                  [op |-> "Free", adr |-> DefaultAdr, val |-> NoVal]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = << >>
  /\ mem = InitMem

IssueRequest(p, r) ==
  /\ regFile[p][r].op = "Free"
  /\ \E a \in Adr, opk \in {"Rd", "Wr"}, v \in Val :
       LET req == [op |-> opk, adr |-> a,
                   val |-> IF opk = "Wr" THEN v ELSE NoVal]
       IN  /\ regFile' = [regFile EXCEPT ![p][r] = req]
           /\ opQ' = [opQ EXCEPT ![p] =
                        Append(@, [req |-> req, reg |-> r, done |-> FALSE,
                                   resp |-> FALSE, val |-> NoVal])]
  /\ UNCHANGED <<opOrder, mem>>

Serialize(p) ==
  \E i \in 1..Len(opQ[p]) :
    /\ ~opQ[p][i].done
    /\ \A j \in 1..(i - 1) : opQ[p][j].done
    /\ LET e == opQ[p][i] IN
         IF e.req.op = "Wr"
           THEN /\ mem' = [mem EXCEPT ![e.req.adr] = e.req.val]
                /\ opQ' = [opQ EXCEPT ![p][i].done = TRUE,
                                      ![p][i].val = e.req.val]
           ELSE /\ mem' = mem
                /\ opQ' = [opQ EXCEPT ![p][i].done = TRUE,
                                      ![p][i].val = mem[e.req.adr]]
    /\ opOrder' = Append(opOrder, [proc |-> p, idx |-> i])
    /\ UNCHANGED regFile

Respond(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ \E i \in 1..Len(opQ[p]) :
       /\ opQ[p][i].reg = r
       /\ opQ[p][i].done
       /\ ~opQ[p][i].resp
       /\ regFile' = [regFile EXCEPT ![p][r] =
                        [op  |-> "Free",
                         adr |-> @.adr,
                         val |-> IF @.op = "Rd" THEN opQ[p][i].val ELSE @.val]]
       /\ opQ' = [opQ EXCEPT ![p][i].resp = TRUE]
  /\ UNCHANGED <<opOrder, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg : IssueRequest(p, r)
  \/ \E p \in Proc : Serialize(p)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)

Fairness ==
  /\ \A p \in Proc : WF_vars(Serialize(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

OpOrderConsistent ==
  /\ \A i \in DOMAIN opOrder :
       /\ opOrder[i].idx \in DOMAIN opQ[opOrder[i].proc]
       /\ opQ[opOrder[i].proc][opOrder[i].idx].done
  /\ \A i, j \in DOMAIN opOrder : (i # j) => (opOrder[i] # opOrder[j])

RespondedImpliesDone ==
  \A p \in Proc : \A i \in DOMAIN opQ[p] : opQ[p][i].resp => opQ[p][i].done

AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
       (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in OpIdSet :
       (oi \in opId) ~> (oi \in CompletedOps)

=============================================================================