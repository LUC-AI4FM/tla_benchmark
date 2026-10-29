---------------------------- MODULE ACP_SB_TLC ----------------------------
(***************************************************************************)
(* TLC-oriented wrapper around the ACP_SB (atomic commitment protocol with *)
(* simple broadcast) specification. The underlying protocol is included   *)
(* here so that the module is self-contained.                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,   \* set of participants
          yes, no,        \* votes
          undecided, commit, abort,  \* decisions
          waiting,        \* coordinator waiting for a vote
          notsent         \* message not yet sent

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type invariant *)

TypeInvParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : BOOLEAN,
                       decision : {undecided, commit, abort},
                       faulty   : BOOLEAN,
                       voteSent : BOOLEAN,
                       forward  : [participants -> {notsent, commit, abort}] ]]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {waiting, yes, no}],
                    alive     : BOOLEAN,
                    decision  : {undecided, commit, abort},
                    broadcast : [participants -> {notsent, commit, abort}],
                    faulty    : BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

---------------------------------------------------------------------------
(* Initial state *)

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
                  alive     |-> TRUE,
                  decision  |-> undecided,
                  broadcast |-> [i \in participants |-> notsent],
                  faulty    |-> FALSE ]

Init == InitParticipant /\ InitCoordinator

---------------------------------------------------------------------------
(* Coordinator actions *)

request(i) ==
  /\ coordinator.alive
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

coordDecide ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \/ \A i \in participants : coordinator.vote[i] # waiting
     \/ \E i \in participants : coordinator.vote[i] = no
  /\ coordinator' = [coordinator EXCEPT
                       !.decision = IF \A i \in participants :
                                          coordinator.vote[i] = yes
                                    THEN commit ELSE abort]
  /\ UNCHANGED participant

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

coordFail ==
  /\ coordinator.alive
  /\ \A i \in participants : ~participant[i].faulty
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
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
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

decideOnCoord(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT
                       ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

decideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT
                       ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision # undecided
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT
                       ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

parFail(i) ==
  /\ participant[i].alive
  /\ ~coordinator.faulty
  /\ \A k \in participants : ~participant[k].faulty
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
  \/ \E i \in participants :
        \/ request(i) \/ getVote(i) \/ coordBroadcast(i)
        \/ sendVote(i) \/ abortOnVote(i) \/ decideOnCoord(i) \/ parFail(i)
        \/ \E j \in participants : decideOnForward(i, j) \/ forward(i, j)
  \/ coordDecide
  \/ coordFail

Fairness ==
  /\ WF_vars(coordDecide)
  /\ \A i \in participants :
        /\ WF_vars(request(i))
        /\ WF_vars(getVote(i))
        /\ WF_vars(coordBroadcast(i))
        /\ WF_vars(sendVote(i))
        /\ WF_vars(abortOnVote(i))
        /\ WF_vars(decideOnCoord(i))
        /\ \A j \in participants :
              /\ WF_vars(decideOnForward(i, j))
              /\ WF_vars(forward(i, j))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties of the protocol *)

AC1 == \A i, j \in participants :
         ~ (participant[i].decision = commit /\ participant[j].decision = abort)

AC3_1 == (\E i \in participants : participant[i].decision = commit)
           => \A j \in participants : participant[j].vote = yes

---------------------------------------------------------------------------
(* TLC wrapper definitions *)

Perms == Permutations(participants)

(* AC4: decisions are irreversible, stated explicitly as a stuttering-   *)
(* invariant temporal formula over the participant variable.           *)
AC4_alt ==
  [][ \A i \in participants :
        /\ (participant[i].decision = commit => participant'[i].decision = commit)
        /\ (participant[i].decision = abort  => participant'[i].decision = abort)
    ]_participant

(* Every participant eventually reaches commit or abort. *)
AllDecide ==
  \A i \in participants : <>(participant[i].decision \in {commit, abort})

=============================================================================