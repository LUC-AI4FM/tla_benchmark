------------------------------- MODULE MC_ACP_NB -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,
          yes, no,
          undecided, commit, abort,
          waiting,
          notsent

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

-----------------------------------------------------------------------------
TypeOK ==
  /\ participant \in [participants ->
        [vote : {yes, no},
         alive : BOOLEAN,
         decision : {undecided, commit, abort},
         voteSent : BOOLEAN,
         forward : [participants -> {notsent, commit, abort}]]]
  /\ coordinator \in
        [request : [participants -> BOOLEAN],
         vote : [participants -> {waiting, yes, no}],
         broadcast : [participants -> {notsent, commit, abort}],
         decision : {undecided, commit, abort},
         alive : BOOLEAN]

InitNB ==
  /\ participant \in [participants ->
        [vote : {yes, no},
         alive : {TRUE},
         decision : {undecided},
         voteSent : {FALSE},
         forward : {[j \in participants |-> notsent]}]]
  /\ coordinator = [request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    broadcast |-> [i \in participants |-> notsent],
                    decision  |-> undecided,
                    alive     |-> TRUE]

-----------------------------------------------------------------------------
(* Coordinator actions *)

request(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A i \in participants : coordinator.vote[i] \in {yes, no}
  /\ coordinator' = [coordinator EXCEPT !.decision =
                       IF \A i \in participants : coordinator.vote[i] = yes
                       THEN commit ELSE abort]
  /\ UNCHANGED participant

coordBroadcast ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ \A i \in participants : coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast =
                       [i \in participants |-> coordinator.decision]]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

-----------------------------------------------------------------------------
(* Participant actions *)

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

decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT
                       ![i].decision = coordinator.broadcast[i],
                       ![i].forward  = [j \in participants |->
                                          IF j = i THEN notsent
                                          ELSE coordinator.broadcast[i]]]
  /\ UNCHANGED coordinator

decideOnForward(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ \E j \in participants :
       /\ participant[j].forward[i] # notsent
       /\ participant' = [participant EXCEPT
                            ![i].decision = participant[j].forward[i],
                            ![i].forward  = [k \in participants |->
                                               IF k = i THEN notsent
                                               ELSE participant[j].forward[i]]]
  /\ UNCHANGED coordinator

abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ coordinator.broadcast[i] = notsent
  /\ \A j \in participants : participant[j].forward[i] = notsent
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
NextNB ==
  \/ makeDecision
  \/ coordBroadcast
  \/ coordDie
  \/ \E i \in participants :
       \/ request(i)
       \/ getVote(i)
       \/ detectFault(i)
       \/ sendVote(i)
       \/ abortOnVote(i)
       \/ decide(i)
       \/ decideOnForward(i)
       \/ abortOnTimeout(i)
       \/ parDie(i)

FairnessNB ==
  /\ WF_vars(makeDecision)
  /\ WF_vars(coordBroadcast)
  /\ \A i \in participants :
       /\ WF_vars(request(i))
       /\ WF_vars(getVote(i))
       /\ WF_vars(detectFault(i))
       /\ WF_vars(sendVote(i))
       /\ WF_vars(abortOnVote(i))
       /\ WF_vars(decide(i))
       /\ WF_vars(decideOnForward(i))
       /\ WF_vars(abortOnTimeout(i))

SpecNB == InitNB /\ [][NextNB]_vars /\ FairnessNB

-----------------------------------------------------------------------------
(* Properties *)

AC1 == [] \A i, j \in participants :
          ~(participant[i].decision = commit /\ participant[j].decision = abort)

AC2 == [] \A i \in participants :
          participant[i].decision = commit =>
             \A j \in participants : participant[j].vote = yes

AC3_1 == [] ((\E i \in participants : participant[i].decision = abort) =>
               \/ \E j \in participants : participant[j].vote = no
               \/ \E j \in participants : ~participant[j].alive
               \/ ~coordinator.alive)

AC3_2 == ( /\ [](coordinator.alive /\ \A i \in participants : participant[i].alive)
           /\ \A i \in participants : participant[i].vote = yes )
         => <>(\A i \in participants : participant[i].decision = commit)

(* Alternative formulation of decision stability, handled efficiently by TLC *)
AC4_alt == [][\A i \in participants :
                 participant[i].decision \in {commit, abort} =>
                    participant'[i].decision = participant[i].decision]_vars

AC5 == <>(\A i \in participants :
            participant[i].alive => participant[i].decision \in {commit, abort})

Perms == Permutations(participants)

=============================================================================