MODULE AtomicCommit
EXTENDS Naturals, Sequences

CONSTANT P \* Set of process identifiers

(* --VARIABLES--------------------------------------------------------- *)
VARIABLES vote, crashed, suspected, status, inbox

(* --TYPES------------------------------------------------------------- *)
VoteValues == {"YES","NO"}
StatusValues == {"INIT","COMMIT","ABORT"}
MsgTypes == {"PREPARE","VOTE_YES","VOTE_NO","COMMIT","ABORT"}

TypeInvariant ==
  /\ vote \in [P -> VoteValues]
  /\ crashed \in [P -> BOOLEAN]
  /\ suspected \in [P -> BOOLEAN]
  /\ status \in [P -> StatusValues]
  /\ inbox \in [P -> SUBSET MsgTypes]

(* --INITIAL STATE----------------------------------------------------- *)
Init ==
  /\ crash = [p |-> FALSE : p \in P]
  /\ suspected = [p |-> FALSE : p \in P]
  /\ status = [p |-> "INIT" : p \in P]
  /\ inbox = [p |-> {} : p \in P]
  /\ (* specialized initial votes: either all YES or all NO *)
     \/ vote = [p |-> "YES" : p \in P]
     \/ vote = [p |-> "NO" : p \in P]

(* --ACTIONS----------------------------------------------------------- *)

SendMsg ==
  /\ UNCHANGED <<crashed, suspected, status, inbox>>
  /\ \E sender \in P :
        /\ ~ crashed[sender]
        /\ content \in MsgTypes
        /\ inbox' = [inbox EXCEPT ![p] = @ \cup {content} : p \in P \{sender}]
  /\ vote' = vote

ReceiveMsg ==
  /\ UNCHANGED <<crashed, suspected, vote>>
  /\ \E p \in P :
        /\ ~ crashed[p]
        /\ msg \in inbox[p]
        /\ inbox' = [inbox EXCEPT ![p] = @ \ {msg}]
        /\ status' =
            IF msg = "COMMIT" THEN [status EXCEPT ![p] = "COMMIT"]
            ELSEIF msg = "ABORT" THEN [status EXCEPT ![p] = "ABORT"]
            ELSE status
  /\ crashed' = crashed
  /\ suspected' = suspected

Crash ==
  /\ UNCHANGED <<vote, suspected, status, inbox>>
  /\ \E p \in P : ~ crashed[p]
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]

Suspect ==
  /\ UNCHANGED <<vote, crashed, status, inbox>>
  /\ \E p \in P : ~ suspected[p]
  /\ suspected' = [suspected EXCEPT ![p] = TRUE]

DecideCommit ==
  /\ UNCHANGED <<crashed, suspected, vote, inbox>>
  /\ \E p \in P :
        /\ status[p] = "INIT"
        /\ (* commit condition: all non-crashed processes voted YES and none are suspected *)
           (\A q \in P : crashed[q] \/ (vote[q]="YES")) 
           /\ ~(\E q \in P : crashed[q] /\ suspected[q])
  /\ status' = [status EXCEPT ![p] = "COMMIT"]

DecideAbort ==
  /\ UNCHANGED <<crashed, suspected, vote, inbox>>
  /\ \E p \in P :
        /\ status[p] = "INIT"
        /\ (* abort if any NO vote or a suspicion exists *)
           (\E q \in P : ~crashed[q] /\ vote[q]="NO") \/ (\E q \in P : suspected[q])
  /\ status' = [status EXCEPT ![p] = "ABORT"]

Next == SendMsg \/ ReceiveMsg \/ Crash \/ Suspect \/ DecideCommit \/ DecideAbort

(* --INVARIANTS------------------------------------------------------- *)

AgreementInv ==
  AG ( (\A i,j \in P :
          (status[i]="COMMIT" /\ status[j]="COMMIT") => TRUE) )

AbortValidityInv ==
  AG ( (\A p \in P : vote[p]="NO" => status[p] # "COMMIT") )

CommitValidityInv ==
  AG ( (\A p \in P : vote[p]="YES" => status[p] # "ABORT") )

TerminationInv ==
  AG ( (\A p \in P : crashed[p] \/ status[p] # "INIT") )

(* --LIVENESS PROPERTIES--------------------------------------------- *)

EventualCommit ==
  []~(\E p \in P : status[p] = "INIT") /\ <> (\A p \in P : status[p] = "COMMIT")

(* --SPECIFICATION---------------------------------------------------- *)
Spec == Init /\ [][Next]_ <<vote, crashed, suspected, status, inbox>> 
          /\ WF_vars[Next]

(* --VARIABLES--------------------------------------------------------- *)
VARIABLES vote, crashed, suspected, status, inbox
=============================================================================
