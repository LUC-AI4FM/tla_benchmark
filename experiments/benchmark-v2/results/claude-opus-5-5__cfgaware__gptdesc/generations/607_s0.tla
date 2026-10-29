---------------------------- MODULE MCRTCommit ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS k1, k2, RM

VARIABLES rmState, tmState, resolved

vars == <<rmState, tmState, resolved>>

const_1571478437097222000 == {k1, k2}

RTTypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"pending", "committed", "aborted"}
    /\ resolved \subseteq RM

constr_1571478437097223000 == TRUE

RTInit ==
    /\ rmState = [r \in RM |-> "working"]
    /\ tmState = "pending"
    /\ resolved = {}

RMPrepare(r) ==
    /\ tmState = "pending"
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ UNCHANGED <<tmState, resolved>>

RMChooseToAbort(r) ==
    /\ tmState = "pending"
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, resolved>>

TMCommit ==
    /\ tmState = "pending"
    /\ \A r \in RM : rmState[r] = "prepared"
    /\ tmState' = "committed"
    /\ UNCHANGED <<rmState, resolved>>

TMAbort ==
    /\ tmState = "pending"
    /\ tmState' = "aborted"
    /\ UNCHANGED <<rmState, resolved>>

Resolve(r) ==
    /\ tmState # "pending"
    /\ r \notin resolved
    /\ rmState' = [rmState EXCEPT ![r] = tmState]
    /\ resolved' = resolved \cup {r}
    /\ UNCHANGED tmState

RTNext ==
    \/ \E r \in RM : RMPrepare(r) \/ RMChooseToAbort(r) \/ Resolve(r)
    \/ TMCommit
    \/ TMAbort

RTSpec ==
    /\ RTInit
    /\ [][RTNext]_vars
    /\ WF_vars(TMAbort)
    /\ \A r \in RM : WF_vars(Resolve(r))

CommitConsistency ==
    \A r1, r2 \in RM :
        ~(rmState[r1] = "committed" /\ rmState[r2] = "aborted")

ResolvedConsistency ==
    \A r \in resolved : rmState[r] = tmState

ResolveLiveness ==
    <>(\A r \in RM : r \in resolved)

=============================================================================