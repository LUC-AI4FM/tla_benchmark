------------------------- MODULE VoucherCancel2PC -------------------------
(***************************************************************************)
(* Two-phase-commit style voucher cancellation protocol.                   *)
(* One coordinator (C), a set of voucher holders (H) and a set of voucher  *)
(* issuers (I) cooperate to cancel vouchers (V).  Each voucher is handled  *)
(* as an independent transaction.  Holders and issuers may independently   *)
(* prepare to cancel or abort.  Prepared participants notify the           *)
(* coordinator.  The coordinator commits the cancellation of a voucher     *)
(* only when every holder and every issuer has reported "prepared".        *)
(* Otherwise it may abort.  Its decision is broadcast to all participants. *)
(* Messages are appended to an abstract set and are never removed.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,      \* set of vouchers
    H,      \* set of voucher holders
    I       \* set of voucher issuers

ASSUME V # {} /\ IsFiniteSet(V) /\ IsFiniteSet(H) /\ IsFiniteSet(I)

VARIABLES
    vState,     \* vState[v]   : lifecycle state of voucher v
    vlcState,   \* vlcState[v] : whether voucher v's lifecycle is still working
    hState,     \* hState[h][v]: state of holder h in the transaction for v
    iState,     \* iState[i][v]: state of issuer i in the transaction for v
    cState,     \* cState[v]   : coordinator state for the transaction for v
    hPrepared,  \* hPrepared[v]: holders from which C received Prepared for v
    iPrepared,  \* iPrepared[v]: issuers from which C received Prepared for v
    msgs        \* set of all messages ever sent

vars == << vState, vlcState, hState, iState, cState,
           hPrepared, iPrepared, msgs >>

PStates == {"waiting", "prepared", "cancelled", "aborted"}

Messages ==
         [type : {"HPrepared"}, vch : V, h : H]
    \cup [type : {"IPrepared"}, vch : V, i : I]
    \cup [type : {"Commit", "Abort"}, vch : V]

-----------------------------------------------------------------------------
(* Type safety *)
TypeOK ==
    /\ vState    \in [V -> {"valid", "cancelled"}]
    /\ vlcState  \in [V -> {"working", "done"}]
    /\ hState    \in [H -> [V -> PStates]]
    /\ iState    \in [I -> [V -> PStates]]
    /\ cState    \in [V -> {"init", "commit", "abort"}]
    /\ hPrepared \in [V -> SUBSET H]
    /\ iPrepared \in [V -> SUBSET I]
    /\ msgs      \subseteq Messages

-----------------------------------------------------------------------------
(* Initial state: all vouchers valid and working, participants idle. *)
Init ==
    /\ vState    = [v \in V |-> "valid"]
    /\ vlcState  = [v \in V |-> "working"]
    /\ hState    = [h \in H |-> [v \in V |-> "waiting"]]
    /\ iState    = [i \in I |-> [v \in V |-> "waiting"]]
    /\ cState    = [v \in V |-> "init"]
    /\ hPrepared = [v \in V |-> {}]
    /\ iPrepared = [v \in V |-> {}]
    /\ msgs      = {}

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h, v) ==
    /\ hState[h][v] = "waiting"
    /\ hState' = [hState EXCEPT ![h][v] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "HPrepared", vch |-> v, h |-> h]}
    /\ UNCHANGED << vState, vlcState, iState, cState, hPrepared, iPrepared >>

HChooseToAbort(h, v) ==
    /\ hState[h][v] = "waiting"
    /\ hState' = [hState EXCEPT ![h][v] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, cState,
                    hPrepared, iPrepared, msgs >>

HRcvCommitMsg(h, v) ==
    /\ [type |-> "Commit", vch |-> v] \in msgs
    /\ hState[h][v] # "cancelled"
    /\ hState' = [hState EXCEPT ![h][v] = "cancelled"]
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED << iState, cState, hPrepared, iPrepared, msgs >>

HRcvAbortMsg(h, v) ==
    /\ [type |-> "Abort", vch |-> v] \in msgs
    /\ hState[h][v] # "aborted"
    /\ hState' = [hState EXCEPT ![h][v] = "aborted"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED << vState, iState, cState, hPrepared, iPrepared, msgs >>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i, v) ==
    /\ iState[i][v] = "waiting"
    /\ iState' = [iState EXCEPT ![i][v] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "IPrepared", vch |-> v, i |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, cState, hPrepared, iPrepared >>

IChooseToAbort(i, v) ==
    /\ iState[i][v] = "waiting"
    /\ iState' = [iState EXCEPT ![i][v] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, cState,
                    hPrepared, iPrepared, msgs >>

IRcvCommitMsg(i, v) ==
    /\ [type |-> "Commit", vch |-> v] \in msgs
    /\ iState[i][v] # "cancelled"
    /\ iState' = [iState EXCEPT ![i][v] = "cancelled"]
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED << hState, cState, hPrepared, iPrepared, msgs >>

IRcvAbortMsg(i, v) ==
    /\ [type |-> "Abort", vch |-> v] \in msgs
    /\ iState[i][v] # "aborted"
    /\ iState' = [iState EXCEPT ![i][v] = "aborted"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED << vState, hState, cState, hPrepared, iPrepared, msgs >>

-----------------------------------------------------------------------------
(* Coordinator actions *)

CRcvHPrepare(h, v) ==
    /\ cState[v] = "init"
    /\ [type |-> "HPrepared", vch |-> v, h |-> h] \in msgs
    /\ h \notin hPrepared[v]
    /\ hPrepared' = [hPrepared EXCEPT ![v] = @ \cup {h}]
    /\ UNCHANGED << vState, vlcState, hState, iState, cState, iPrepared, msgs >>

CRcvIPrepare(i, v) ==
    /\ cState[v] = "init"
    /\ [type |-> "IPrepared", vch |-> v, i |-> i] \in msgs
    /\ i \notin iPrepared[v]
    /\ iPrepared' = [iPrepared EXCEPT ![v] = @ \cup {i}]
    /\ UNCHANGED << vState, vlcState, hState, iState, cState, hPrepared, msgs >>

CCommit(v) ==
    /\ cState[v] = "init"
    /\ hPrepared[v] = H
    /\ iPrepared[v] = I
    /\ cState' = [cState EXCEPT ![v] = "commit"]
    /\ msgs' = msgs \cup {[type |-> "Commit", vch |-> v]}
    /\ UNCHANGED << vState, vlcState, hState, iState, hPrepared, iPrepared >>

CAbort(v) ==
    /\ cState[v] = "init"
    /\ cState' = [cState EXCEPT ![v] = "abort"]
    /\ msgs' = msgs \cup {[type |-> "Abort", vch |-> v]}
    /\ UNCHANGED << vState, vlcState, hState, iState, hPrepared, iPrepared >>

CDecide(v) == CCommit(v) \/ CAbort(v)

-----------------------------------------------------------------------------
Next ==
    \/ \E v \in V :
         \/ \E h \in H : \/ HPrepare(h, v)
                         \/ HChooseToAbort(h, v)
                         \/ HRcvCommitMsg(h, v)
                         \/ HRcvAbortMsg(h, v)
                         \/ CRcvHPrepare(h, v)
         \/ \E i \in I : \/ IPrepare(i, v)
                         \/ IChooseToAbort(i, v)
                         \/ IRcvCommitMsg(i, v)
                         \/ IRcvAbortMsg(i, v)
                         \/ CRcvIPrepare(i, v)
         \/ CCommit(v)
         \/ CAbort(v)

(* Explicit fairness assumptions: the coordinator eventually processes   *)
(* prepared notifications and eventually decides.  Participants          *)
(* eventually learn the coordinator's decision.                          *)
Fairness ==
    /\ \A v \in V :
         /\ WF_vars(CDecide(v))
         /\ WF_vars(CCommit(v))
         /\ \A h \in H : /\ WF_vars(CRcvHPrepare(h, v))
                         /\ WF_vars(HRcvCommitMsg(h, v))
                         /\ WF_vars(HRcvAbortMsg(h, v))
         /\ \A i \in I : /\ WF_vars(CRcvIPrepare(i, v))
                         /\ WF_vars(IRcvCommitMsg(i, v))
                         /\ WF_vars(IRcvAbortMsg(i, v))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No two participants reach conflicting terminal decisions for a voucher.
Consistency ==
    \A v \in V :
        LET states == {hState[h][v] : h \in H} \cup {iState[i][v] : i \in I}
        IN  ~ ("cancelled" \in states /\ "aborted" \in states)

\* Agreement between holders and issuers, stated explicitly.
HolderIssuerAgreement ==
    \A v \in V, h \in H, i \in I :
        /\ ~ (hState[h][v] = "cancelled" /\ iState[i][v] = "aborted")
        /\ ~ (hState[h][v] = "aborted"   /\ iState[i][v] = "cancelled")

\* A voucher is cancelled only if the coordinator committed after
\* receiving prepared notifications from every holder and every issuer.
CancellationSafety ==
    \A v \in V :
        vState[v] = "cancelled" =>
            /\ cState[v] = "commit"
            /\ hPrepared[v] = H
            /\ iPrepared[v] = I

\* A participant finalizes as cancelled only after a coordinator commit.
CancelledOnlyAfterCommit ==
    \A v \in V :
        /\ \A h \in H : hState[h][v] = "cancelled" => cState[v] = "commit"
        /\ \A i \in I : iState[i][v] = "cancelled" => cState[v] = "commit"

Invariants ==
    /\ TypeOK
    /\ Consistency
    /\ HolderIssuerAgreement
    /\ CancellationSafety
    /\ CancelledOnlyAfterCommit

-----------------------------------------------------------------------------
(* Liveness properties *)

AllPrepared(v) ==
    /\ \A h \in H : hState[h][v] = "prepared"
    /\ \A i \in I : iState[i][v] = "prepared"

\* When every participant has prepared, the coordinator eventually decides.
PreparedLeadsToDecision ==
    \A v \in V : AllPrepared(v) ~> (cState[v] \in {"commit", "abort"})

\* Every transaction eventually gets a coordinator decision.
EventualDecision ==
    \A v \in V : <>(cState[v] \in {"commit", "abort"})

\* Once committed, the voucher is eventually cancelled.
CommitLeadsToCancel ==
    \A v \in V : (cState[v] = "commit") ~> (vState[v] = "cancelled")

\* Every voucher's lifecycle eventually leaves the working state
\* (when there is at least one participant to act on the decision).
EventualCompletion ==
    (H \cup I # {}) => \A v \in V : <>(vlcState[v] = "done")

THEOREM Spec => []Invariants
=============================================================================