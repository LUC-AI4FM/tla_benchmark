------------------------------- MODULE AsyncCommit --------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs \* Set of processes
    FD \* Failure detector mapping process to set of suspected processes

VARIABLES 
    vote,       \* vote[p] is the initial vote of process p (YES or NO)
    msg,        \* msg[p][q] is the message sent from p to q
    committed,  \* committed[p] indicates if process p has committed
    aborted     \* aborted[p] indicates if process p has aborted

Init == 
    /\ (\E v \in {YES, NO} : \A p \in Procs : vote[p] = v)
    /\ (\A p \in Procs : msg[p] = <<>>)
    /\ (\A p \in Procs : committed[p] = FALSE)
    /\ (\A p \in Procs : aborted[p] = FALSE)

Next == 
    \/ \E p \in Procs, q \in (Procs \ {p}) \ FD[p], m \in {YES, NO} :
        \* Process p sends message m to process q
        \/ msg' = [msg EXCEPT ![p][q] = <<m>>]
        /\ UNCHANGED <<vote, committed, aborted>>
    \/ \E p \in Procs :
        \* Process p receives messages and updates state
        \/ aborted'[p] = (/\ ~committed[p]
                          /\ (\E q \in (Procs \ {p}) \ FD[p], m \in msg[q][p] : m = NO))
        \/ committed'[p] = (/\ ~aborted[p]
                           /\ (\A q \in Procs \ {p} : (q \notin FD[p] => <<YES>> \in SUBSEQ(msg[q][p]))))
        /\ UNCHANGED <<vote, msg>>
    \/ \E p \in Procs :
        \* Process p commits or aborts based on its state
        \/ aborted'[p] = TRUE \/ committed'[p] = TRUE
        /\ UNCHANGED <<vote, msg>>

Spec == 
    Init /\ [][Next]_<<msg, committed, aborted>> /\ WF_next(<<msg, committed, aborted>>)

\* Type Invariants
TypeOK ==
    /\ \A p \in Procs : vote[p] \in {YES, NO}
    /\ \A p \in Procs : msg[p] \in [Procs -> Seq({YES, NO})]
    /\ \A p \in Procs : committed[p] \in BOOLEAN
    /\ \A p \in Procs : aborted[p] \in BOOLEAN

\* Safety Properties
Agreement == 
    \/ (\A p \in Procs : committed[p])
    \/ (\A p \in Procs : aborted[p])

AbortValidity ==
    \A p \in Procs :
        aborted[p] => (\E q \in (Procs \ {p}) \ FD[p], m \in msg[q][p] : m = NO)

CommitValidity ==
    \A p \in Procs :
        committed[p] => (\A q \in Procs \ {p} : (q \notin FD[p] => <<YES>> \in SUBSEQ(msg[q][p])))

Termination ==
    \A p \in Procs :
        \/ aborted[p]
        \/ committed[p]

\* Liveness Properties
EventualCommit ==
    <>(\A p \in Procs : committed[p])

WF_next == WF_<<msg, committed, aborted>>(Next)

=============================================================================