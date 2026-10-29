--------------------------- MODULE NBACReliableBroadcast ---------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Participant

ASSUME Participant # {}

Decision    == {"undecided", "commit", "abort"}
FwdState    == {"notsent", "commit", "abort"}
CVoteState  == {"waiting", "yes", "no"}
BcastState  == {"none", "commit", "abort"}

VARIABLES
    coordinator,   \* coordinator state
    participant,   \* participant state
    forward        \* forward[p][q] : what participant p has forwarded to q

vars == << coordinator, participant, forward >>

-----------------------------------------------------------------------------
(* Base atomic commitment state *)

TypeOK ==
    /\ coordinator \in [ request   : [Participant -> BOOLEAN],
                         vote      : [Participant -> CVoteState],
                         broadcast : [Participant -> BcastState],
                         decision  : Decision,
                         faulty    : BOOLEAN ]
    /\ participant \in [Participant ->
                         [ vote        : {"yes", "no"},
                           alive       : BOOLEAN,
                           faulty      : BOOLEAN,
                           voteSent    : BOOLEAN,
                           predecision : Decision,
                           decision    : Decision ]]
    /\ forward \in [Participant -> [Participant -> FwdState]]

Init ==
    /\ coordinator = [ request   |-> [p \in Participant |-> FALSE],
                       vote      |-> [p \in Participant |-> "waiting"],
                       broadcast |-> [p \in Participant |-> "none"],
                       decision  |-> "undecided",
                       faulty    |-> FALSE ]
    /\ participant \in [Participant ->
                         [ vote        : {"yes", "no"},
                           alive       : {TRUE},
                           faulty      : {FALSE},
                           voteSent    : {FALSE},
                           predecision : {"undecided"},
                           decision    : {"undecided"} ]]
    /\ forward = [p \in Participant |-> [q \in Participant |-> "notsent"]]

-----------------------------------------------------------------------------
(* Coordinator actions *)

CRequestVote(p) ==
    /\ ~coordinator.faulty
    /\ coordinator.decision = "undecided"
    /\ ~coordinator.request[p]
    /\ coordinator' = [coordinator EXCEPT !.request[p] = TRUE]
    /\ UNCHANGED << participant, forward >>

CRecvVote(p) ==
    /\ ~coordinator.faulty
    /\ coordinator.decision = "undecided"
    /\ participant[p].voteSent
    /\ coordinator.vote[p] = "waiting"
    /\ coordinator' = [coordinator EXCEPT !.vote[p] = participant[p].vote]
    /\ UNCHANGED << participant, forward >>

CDecideCommit ==
    /\ ~coordinator.faulty
    /\ coordinator.decision = "undecided"
    /\ \A p \in Participant : coordinator.vote[p] = "yes"
    /\ coordinator' = [coordinator EXCEPT !.decision = "commit"]
    /\ UNCHANGED << participant, forward >>

CDecideAbort ==
    /\ ~coordinator.faulty
    /\ coordinator.decision = "undecided"
    /\ \E p \in Participant : coordinator.vote[p] = "no"
    /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
    /\ UNCHANGED << participant, forward >>

\* Simulated coordinator timeout: a participant crashed before its vote arrived
CTimeoutAbort ==
    /\ ~coordinator.faulty
    /\ coordinator.decision = "undecided"
    /\ \E p \in Participant : participant[p].faulty /\ coordinator.vote[p] = "waiting"
    /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
    /\ UNCHANGED << participant, forward >>

CBroadcast(p) ==
    /\ ~coordinator.faulty
    /\ coordinator.decision # "undecided"
    /\ coordinator.broadcast[p] = "none"
    /\ coordinator' = [coordinator EXCEPT !.broadcast[p] = coordinator.decision]
    /\ UNCHANGED << participant, forward >>

CFail ==
    /\ ~coordinator.faulty
    /\ coordinator' = [coordinator EXCEPT !.faulty = TRUE]
    /\ UNCHANGED << participant, forward >>

-----------------------------------------------------------------------------
(* Participant actions *)

PSendVote(p) ==
    /\ participant[p].alive
    /\ coordinator.request[p]
    /\ ~participant[p].voteSent
    /\ participant' = [participant EXCEPT ![p].voteSent = TRUE]
    /\ UNCHANGED << coordinator, forward >>

PFail(p) ==
    /\ participant[p].alive
    /\ participant' = [participant EXCEPT ![p].alive = FALSE,
                                          ![p].faulty = TRUE]
    /\ UNCHANGED << coordinator, forward >>

\* Pre-decide on a decision received from the coordinator
PPreDecideOnCoord(p) ==
    /\ participant[p].alive
    /\ participant[p].predecision = "undecided"
    /\ coordinator.broadcast[p] # "none"
    /\ participant' = [participant EXCEPT ![p].predecision = coordinator.broadcast[p]]
    /\ UNCHANGED << coordinator, forward >>

\* Pre-decide on a decision forwarded by another participant
PPreDecideOnForward(p, q) ==
    /\ p # q
    /\ participant[p].alive
    /\ participant[p].predecision = "undecided"
    /\ forward[q][p] # "notsent"
    /\ participant' = [participant EXCEPT ![p].predecision = forward[q][p]]
    /\ UNCHANGED << coordinator, forward >>

\* Forward the pre-decision to another participant (reliable broadcast)
PForward(p, q) ==
    /\ p # q
    /\ participant[p].alive
    /\ participant[p].predecision # "undecided"
    /\ forward[p][q] = "notsent"
    /\ forward' = [forward EXCEPT ![p][q] = participant[p].predecision]
    /\ UNCHANGED << coordinator, participant >>

ForwardingComplete(p) ==
    \A q \in Participant \ {p} : forward[p][q] # "notsent"

\* Deliver (decide) only after forwarding to all other participants
PDecide(p) ==
    /\ participant[p].alive
    /\ participant[p].predecision # "undecided"
    /\ participant[p].decision = "undecided"
    /\ ForwardingComplete(p)
    /\ participant' = [participant EXCEPT ![p].decision = participant[p].predecision]
    /\ UNCHANGED << coordinator, forward >>

\* A participant that voted "no" may unilaterally abort
PAbortOnNoVote(p) ==
    /\ participant[p].alive
    /\ participant[p].vote = "no"
    /\ participant[p].predecision = "undecided"
    /\ participant' = [participant EXCEPT ![p].predecision = "abort"]
    /\ UNCHANGED << coordinator, forward >>

\* Simulated timeout: coordinator crashed and no live participant holds
\* or has been sent any decision.
TimeoutCondition ==
    /\ coordinator.faulty
    /\ \A q \in Participant :
         participant[q].alive =>
            /\ participant[q].predecision = "undecided"
            /\ coordinator.broadcast[q] = "none"
            /\ \A r \in Participant : forward[r][q] = "notsent"

PAbortOnTimeout(p) ==
    /\ participant[p].alive
    /\ participant[p].predecision = "undecided"
    /\ TimeoutCondition
    /\ participant' = [participant EXCEPT ![p].predecision = "abort"]
    /\ UNCHANGED << coordinator, forward >>

-----------------------------------------------------------------------------
(* Specification *)

CoordinatorNext ==
    \/ \E p \in Participant : CRequestVote(p) \/ CRecvVote(p) \/ CBroadcast(p)
    \/ CDecideCommit
    \/ CDecideAbort
    \/ CTimeoutAbort

ParticipantNext ==
    \E p \in Participant :
        \/ PSendVote(p)
        \/ PPreDecideOnCoord(p)
        \/ \E q \in Participant : PPreDecideOnForward(p, q)
        \/ \E q \in Participant : PForward(p, q)
        \/ PDecide(p)
        \/ PAbortOnNoVote(p)
        \/ PAbortOnTimeout(p)

FailureNext ==
    \/ CFail
    \/ \E p \in Participant : PFail(p)

Next == CoordinatorNext \/ ParticipantNext \/ FailureNext

Fairness ==
    /\ \A p \in Participant :
         /\ WF_vars(CRequestVote(p))
         /\ WF_vars(CRecvVote(p))
         /\ WF_vars(CBroadcast(p))
         /\ WF_vars(PSendVote(p))
         /\ WF_vars(PPreDecideOnCoord(p))
         /\ WF_vars(PDecide(p))
         /\ WF_vars(PAbortOnTimeout(p))
         /\ \A q \in Participant :
              /\ WF_vars(PPreDecideOnForward(p, q))
              /\ WF_vars(PForward(p, q))
    /\ WF_vars(CDecideCommit)
    /\ WF_vars(CDecideAbort)
    /\ WF_vars(CTimeoutAbort)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No two participants decide differently
AC1_Agreement ==
    \A p, q \in Participant :
        (participant[p].decision # "undecided" /\ participant[q].decision # "undecided")
            => participant[p].decision = participant[q].decision

\* Commit only if all participants voted yes
AC2_Validity ==
    (\E p \in Participant : participant[p].decision = "commit")
        => \A q \in Participant : participant[q].vote = "yes"

\* Decisions are irrevocable (action property)
Irrevocable ==
    [][\A p \in Participant :
         participant[p].decision # "undecided"
            => participant'[p].decision = participant[p].decision]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Non-blocking termination: every correct participant eventually decides
Termination ==
    <>[](\A p \in Participant :
            participant[p].alive => participant[p].decision # "undecided")

\* Invalid properties (expected to be violated)
AllCommit ==
    <>(\A p \in Participant : participant[p].decision = "commit")

AllAbort ==
    <>(\A p \in Participant : participant[p].decision = "abort")

AllYesVotesLeadsToCommit ==
    (\A p \in Participant : participant[p].vote = "yes")
        ~> (\A p \in Participant : participant[p].decision = "commit")

=============================================================================