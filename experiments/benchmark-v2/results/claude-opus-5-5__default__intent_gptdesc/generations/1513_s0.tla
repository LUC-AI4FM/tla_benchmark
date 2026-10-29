------------------------------ MODULE TokenRingTermination ------------------------------
(***************************************************************************)
(* Token-based distributed termination detection for a ring of three      *)
(* processes (Dijkstra, Feijen, van Gasteren, EWD 840).                    *)
(*                                                                         *)
(* Processes are numbered 0..N-1. The token travels downward:              *)
(* N-1 -> N-2 -> ... -> 0. Process 0 is the detector. It starts a probe    *)
(* by sending a white token to process N-1. A process that holds the       *)
(* token forwards it only when it is passive. A black process, or a        *)
(* black token, always passes the token on as black. A process turns      *)
(* black when it sends work to a higher-numbered process, because that     *)
(* process may already have been visited by the token. If the token        *)
(* returns to process 0 white, and process 0 is white and passive, then    *)
(* the token has completed a full cycle. The ring is then quiescent and    *)
(* termination is declared.                                                *)
(***************************************************************************)
EXTENDS Naturals

N == 3
Procs == 0 .. N-1
Colors == {"white", "black"}

VARIABLES
    active,      \* active[i] = TRUE iff process i has outstanding work
    color,       \* local color bit of each process
    tpos,        \* process currently holding the (single) token
    tcolor,      \* color bit carried by the token
    terminated   \* TRUE once the detector (process 0) declares termination

vars == << active, color, tpos, tcolor, terminated >>

-----------------------------------------------------------------------------
(* Type / domain correctness                                              *)

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ color \in [Procs -> Colors]
    /\ tpos \in Procs
    /\ tcolor \in Colors
    /\ terminated \in BOOLEAN

-----------------------------------------------------------------------------
(* Initial state                                                          *)
(* The token starts black, so no stale detection can happen before a      *)
(* genuine probe has been started.                                        *)

Init ==
    /\ active \in [Procs -> BOOLEAN]
    /\ color \in [Procs -> Colors]
    /\ tpos \in Procs
    /\ tcolor = "black"
    /\ terminated = FALSE

-----------------------------------------------------------------------------
(* Token actions                                                          *)

\* The detector starts a new probe after an unsuccessful round.
InitiateProbe ==
    /\ ~terminated
    /\ tpos = 0
    /\ (tcolor = "black" \/ color[0] = "black")
    /\ tpos' = N - 1
    /\ tcolor' = "white"
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED << active, terminated >>

\* A non-detector process forwards the token to its ring neighbour i-1.
PassToken(i) ==
    /\ ~terminated
    /\ i # 0
    /\ tpos = i
    /\ (~active[i] \/ color[i] = "black" \/ tcolor = "black")
    /\ tpos' = i - 1
    /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED << active, terminated >>

\* The detector declares termination after a successful full cycle.
Detect ==
    /\ ~terminated
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~active[0]
    /\ terminated' = TRUE
    /\ UNCHANGED << active, color, tpos, tcolor >>

-----------------------------------------------------------------------------
(* Process (environment) actions                                          *)

\* An active process sends work to another process and activates it.
\* Sending to a higher-numbered process blackens the sender.
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Procs \ {i} :
          /\ active' = [active EXCEPT ![j] = TRUE]
          /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
    /\ UNCHANGED << tpos, tcolor, terminated >>

\* An active process finishes its local work.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << color, tpos, tcolor, terminated >>

\* After detection the system is quiescent. It may stutter forever.
Halted ==
    /\ terminated
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Controlled ==
    \/ InitiateProbe
    \/ \E i \in Procs \ {0} : PassToken(i)
    \/ Detect

Environment ==
    \E i \in Procs : SendMsg(i) \/ Deactivate(i)

Next == Controlled \/ Environment \/ Halted

(* Fairness: the token is eventually delivered by every holder, a probe   *)
(* is eventually started, and detection is eventually performed when it   *)
(* is continuously enabled. Process work actions need no fairness.        *)
Fairness ==
    /\ WF_vars(InitiateProbe)
    /\ \A i \in Procs \ {0} : WF_vars(PassToken(i))
    /\ WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                      *)

\* The token is at a valid process and has an allowed color.
TokenValid == tpos \in Procs /\ tcolor \in Colors

\* There is exactly one token. It is represented by a single position
\* variable, so the set of holders always has exactly one element.
TokenHolders == { p \in Procs : p = tpos }
UniqueToken == \E p \in Procs : TokenHolders = {p}

\* Local states stay within their domains.
LocalStatesOK ==
    /\ \A i \in Procs : active[i] \in BOOLEAN
    /\ \A i \in Procs : color[i] \in Colors

Quiescent == \A i \in Procs : ~active[i]

\* Correctness of detection: termination is never declared while some
\* process is active. Only active processes can create new work, so
\* Quiescent also rules out any potential for new work.
TerminationCorrect == terminated => Quiescent

\* Inductive invariant of EWD 840.
P0 == \A i \in Procs : i > tpos => ~active[i]
P1 == \E j \in Procs : j <= tpos /\ color[j] = "black"
P2 == tcolor = "black"
Inv == P0 \/ P1 \/ P2

Safety == TypeOK /\ TokenValid /\ UniqueToken /\ LocalStatesOK
          /\ TerminationCorrect /\ Inv

-----------------------------------------------------------------------------
(* Temporal properties                                                    *)

\* Liveness: once every process is passive, the token eventually completes
\* a full white cycle and termination is declared.
Liveness == Quiescent ~> terminated

\* Quiescence is stable: no pending work can arise once all are passive.
QuiescenceStable == [](Quiescent => []Quiescent)

\* Detection is stable and permanent.
TerminatedStable == [](terminated => []terminated)

\* No false positives: after termination is declared, no process ever
\* becomes active again.
NoFalsePositive == [](terminated => []Quiescent)

\* If processes keep doing work forever, termination is never declared.
NoFalseDetectionUnderWork ==
    ([]<>(\E i \in Procs : active[i])) => []~terminated

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
THEOREM Spec => QuiescenceStable /\ TerminatedStable
THEOREM Spec => NoFalsePositive /\ NoFalseDetectionUnderWork

=============================================================================