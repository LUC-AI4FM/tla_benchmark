---------------------------- MODULE MC_ACP_NB ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants, waiting, notsent, undecided, commit, abort, yes, no

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

-----------------------------------------------------------------------------
TypeInvParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : BOOLEAN,
                       decision : {undecided, commit, abort},
                       faulty   : BOOLEAN,
                       voteSent : BOOLEAN,
                       forward  : [participants -> {notsent, undecided, commit, abort}] ]]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {waiting, yes, no}],
                    broadcast : [participants -> BOOLEAN],
                    decision  : {undecided, commit, abort},
                    alive     : BOOLEAN,
                    faulty    : BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

-----------------------------------------------------------------------------
InitParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : {TRUE},
                       decision : {undecided},
                       faulty   : {FALSE},
                       voteSent : {FALSE},
                       forward  : {[k \in participants |-> notsent]} ]]

InitCoordinator ==
  coordinator = [ request   |-> [i \in participants |-> FALSE],
                  vote      |-> [i \in participants |-> waiting],
                  broadcast |-> [i \in participants |-> FALSE],
                  decision  |-> undecided,
                  alive     |-> TRUE,
                  faulty    |-> FALSE ]

InitNB == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
\* Coordinator actions

request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.request[i]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ coordinator' = [coordinator EXCEPT
                       !.decision = IF \A j \in participants : coordinator.vote[j] = yes
                                      THEN commit ELSE abort]
  /\ UNCHANGED participant

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ ~coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

-----------------------------------------------------------------------------
\* Participant actions

sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

receiveDecision(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

\* Non-blocking extensions

forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision # undecided
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

decideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[j].forward[i] \in {commit, abort}
  /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ ~coordinator.alive
  /\ ~coordinator.broadcast[i]
  /\ \A j \in participants \ {i} :
        /\ participant[j].alive => participant[j].decision = undecided
        /\ participant[j].forward[i] \notin {commit, abort}
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
CoordinatorNext ==
  \/ \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
  \/ makeDecision
  \/ coordDie

ParticipantNext ==
  \E i \in participants :
     \/ sendVote(i) \/ abortOnVote(i) \/ receiveDecision(i)
     \/ abortOnTimeoutRequest(i) \/ abortOnTimeout(i) \/ parDie(i)
     \/ \E j \in participants : forward(i, j) \/ decideOnForward(i, j)

NextNB == CoordinatorNext \/ ParticipantNext

FairnessNB ==
  /\ \A i \in participants :
       /\ WF_vars(request(i))
       /\ WF_vars(getVote(i))
       /\ WF_vars(detectFault(i))
       /\ WF_vars(coordBroadcast(i))
       /\ WF_vars(sendVote(i))
       /\ WF_vars(abortOnVote(i))
       /\ WF_vars(receiveDecision(i))
       /\ WF_vars(abortOnTimeoutRequest(i))
       /\ WF_vars(abortOnTimeout(i))
       /\ \A j \in participants :
            /\ WF_vars(forward(i, j))
            /\ WF_vars(decideOnForward(i, j))
  /\ WF_vars(makeDecision)

SpecNB == InitNB /\ [][NextNB]_vars /\ FairnessNB

-----------------------------------------------------------------------------
\* Properties

Decided(i) == participant[i].decision \in {commit, abort}

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          (Decided(i) /\ Decided(j)) => participant[i].decision = participant[j].decision

\* Commit only if all participants voted yes
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
             => (\A j \in participants : participant[j].vote = yes) )

\* If any participant votes no, abort is the only possible decision
AC3_1 == [] ( (\E i \in participants : participant[i].vote = no)
               => (\A j \in participants : participant[j].decision # commit) )

\* If there are no failures and all vote yes, the decision will be commit
AC3_2 == ( /\ \A i \in participants : participant[i].vote = yes
           /\ [] (\A i \in participants : participant[i].alive)
           /\ [] coordinator.alive )
         => <> (\A i \in participants : participant[i].decision = commit)

\* Decisions are irreversible (reformulated as an action property)
AC4_alt == [][ \A i \in participants :
                 Decided(i) => participant'[i].decision = participant[i].decision ]_vars

\* Every alive participant eventually decides
AC5 == <> \A i \in participants :
            participant[i].alive => Decided(i)

\* Every participant eventually commits (expected to be violated)
AllMustCommit == <> \A i \in participants : participant[i].decision = commit

\* Symmetry
Perms == Permutations(participants)

-----------------------------------------------------------------------------
\* Concrete counterexample witness (encoded as plain data)

PostCondition ==
  [ property   |-> "AllMustCommit",
    participantsUsed |-> <<"p0", "p1">>,
    trace |->
      << [ step |-> 1, action |-> "Init",
           p0 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           p1 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           coord |-> [alive |-> TRUE,  decision |-> "undecided"] ],
         [ step |-> 2, action |-> "request(p0)",
           p0 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           p1 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           coord |-> [alive |-> TRUE,  decision |-> "undecided"] ],
         [ step |-> 3, action |-> "coordDie",
           p0 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           p1 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           coord |-> [alive |-> FALSE, decision |-> "undecided"] ],
         [ step |-> 4, action |-> "abortOnTimeoutRequest(p1)",
           p0 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           p1 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "abort"],
           coord |-> [alive |-> FALSE, decision |-> "undecided"] ],
         [ step |-> 5, action |-> "parDie(p1)",
           p0 |-> [vote |-> "yes", alive |-> TRUE,  decision |-> "undecided"],
           p1 |-> [vote |-> "yes", alive |-> FALSE, decision |-> "abort"],
           coord |-> [alive |-> FALSE, decision |-> "undecided"] ],
         [ step |-> 6, action |-> "parDie(p0)",
           p0 |-> [vote |-> "yes", alive |-> FALSE, decision |-> "undecided"],
           p1 |-> [vote |-> "yes", alive |-> FALSE, decision |-> "abort"],
           coord |-> [alive |-> FALSE, decision |-> "undecided"] ] >>,
    stuttering |-> TRUE,
    distinctStatesVisited |-> 6 ]

=============================================================================