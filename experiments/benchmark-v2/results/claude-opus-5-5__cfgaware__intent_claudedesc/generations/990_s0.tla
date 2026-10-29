---------------------------- MODULE NBAC ----------------------------
EXTENDS Naturals, FiniteSets

N == 3
P == 1..N

Decisions == {"commit", "abort"}

VARIABLES vote, pc, crashed, inbox, decision,
          cState, cDecision, cCrashed, sent

vars == <<vote, pc, crashed, inbox, decision,
          cState, cDecision, cCrashed, sent>>

TypeOK ==
  /\ vote \in [P -> {"yes", "no"}]
  /\ pc \in [P -> {"init", "voted", "decided"}]
  /\ crashed \in [P -> BOOLEAN]
  /\ inbox \in [P -> SUBSET Decisions]
  /\ decision \in [P -> {"none", "commit", "abort"}]
  /\ cState \in {"wait", "decided"}
  /\ cDecision \in {"none", "commit", "abort"}
  /\ cCrashed \in BOOLEAN
  /\ sent \subseteq P

Init ==
  /\ vote \in [P -> {"yes", "no"}]
  /\ pc = [p \in P |-> "init"]
  /\ crashed = [p \in P |-> FALSE]
  /\ inbox = [p \in P |-> {}]
  /\ decision = [p \in P |-> "none"]
  /\ cState = "wait"
  /\ cDecision = "none"
  /\ cCrashed = FALSE
  /\ sent = {}

Voted == {p \in P : pc[p] # "init"}

\* Participant p sends its vote to the coordinator
Vote(p) ==
  /\ ~crashed[p]
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "voted"]
  /\ UNCHANGED <<vote, crashed, inbox, decision, cState, cDecision, cCrashed, sent>>

\* Coordinator decides once every participant has voted or is known to have crashed
CDecide ==
  /\ ~cCrashed
  /\ cState = "wait"
  /\ \A q \in P : q \in Voted \/ crashed[q]
  /\ cDecision' = IF \A q \in P : q \in Voted /\ vote[q] = "yes"
                    THEN "commit" ELSE "abort"
  /\ cState' = "decided"
  /\ UNCHANGED <<vote, pc, crashed, inbox, decision, cCrashed, sent>>

\* Coordinator sends its decision to participant p (one at a time)
CSend(p) ==
  /\ ~cCrashed
  /\ cState = "decided"
  /\ p \notin sent
  /\ sent' = sent \cup {p}
  /\ inbox' = [inbox EXCEPT ![p] = @ \cup {cDecision}]
  /\ UNCHANGED <<vote, pc, crashed, decision, cState, cDecision, cCrashed>>

CCrash ==
  /\ ~cCrashed
  /\ cCrashed' = TRUE
  /\ UNCHANGED <<vote, pc, crashed, inbox, decision, cState, cDecision, sent>>

\* Reliable broadcast: forward to all others, then decide
Receive(p) ==
  /\ ~crashed[p]
  /\ pc[p] = "voted"
  /\ \E d \in inbox[p] :
       /\ inbox' = [q \in P |-> IF q = p THEN inbox[q] ELSE inbox[q] \cup {d}]
       /\ decision' = [decision EXCEPT ![p] = d]
  /\ pc' = [pc EXCEPT ![p] = "decided"]
  /\ UNCHANGED <<vote, crashed, cState, cDecision, cCrashed, sent>>

\* Coordinator failed and no live participant holds any decision: abort safely
Timeout(p) ==
  /\ ~crashed[p]
  /\ pc[p] = "voted"
  /\ cCrashed
  /\ inbox[p] = {}
  /\ \A q \in P : ~crashed[q] => inbox[q] = {}
  /\ inbox' = [q \in P |-> IF q = p THEN inbox[q] ELSE inbox[q] \cup {"abort"}]
  /\ decision' = [decision EXCEPT ![p] = "abort"]
  /\ pc' = [pc EXCEPT ![p] = "decided"]
  /\ UNCHANGED <<vote, crashed, cState, cDecision, cCrashed, sent>>

PCrash(p) ==
  /\ ~crashed[p]
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, pc, inbox, decision, cState, cDecision, cCrashed, sent>>

Next ==
  \/ CDecide
  \/ CCrash
  \/ \E p \in P : Vote(p) \/ CSend(p) \/ Receive(p) \/ Timeout(p) \/ PCrash(p)

Fairness ==
  /\ WF_vars(CDecide)
  /\ \A p \in P : /\ WF_vars(Vote(p))
                  /\ WF_vars(CSend(p))
                  /\ WF_vars(Receive(p))
                  /\ WF_vars(Timeout(p))

SpecNB == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Correctness properties

Agreement ==
  \A p, q \in P :
     (decision[p] # "none" /\ decision[q] # "none") => decision[p] = decision[q]

Integrity ==
  [][\A p \in P : decision[p] # "none" => decision'[p] = decision[p]]_vars

NoFailures == ~cCrashed /\ \A p \in P : ~crashed[p]

\* Validity (commit): all vote yes and no failures => everyone commits
AllCommit ==
  ((\A p \in P : vote[p] = "yes") /\ []NoFailures)
     => <>(\A p \in P : decision[p] = "commit")

\* Validity (abort): any "no" vote => never commit, and every live participant aborts
AllAbort ==
  (\E p \in P : vote[p] = "no")
     => /\ [](\A p \in P : decision[p] # "commit")
        /\ <>(\A p \in P : crashed[p] \/ decision[p] = "abort")

\* Termination / non-blocking
Termination ==
  <>(\A p \in P : crashed[p] \/ decision[p] # "none")

=============================================================================