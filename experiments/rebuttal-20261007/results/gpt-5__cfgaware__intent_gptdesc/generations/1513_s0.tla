------------------------------ MODULE TerminationTokenRing3 ------------------------------

EXTENDS Naturals

(*
  Token-passing termination detection for a fixed ring of three processes.
  A single circulating token carries a color bit. Each process maintains:
    - active[i] : whether it has outstanding (local) work or incoming messages to process
    - lcolor[i] : a local color bit
    - work[i]   : count of outstanding local work items
    - msgs[i]   : count of incoming messages destined to process i (abstracting work in transit)
  The token resides at exactly one process tokenAt ∈ Proc and carries tokenColor ∈ Color.
  Termination is declared by setting term = TRUE, after a white token completes a full cycle
  and the system is globally quiescent.
*)

(***************************************************************************)
(* Constants and basic sets                                                *)
(***************************************************************************)

N == 3
Proc == 0..(N - 1)
Color == {0, 1}

NextProc(i) == IF i = N - 1 THEN 0 ELSE i + 1

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  active,      \* [Proc -> BOOLEAN]
  lcolor,      \* [Proc -> Color]
  work,        \* [Proc -> Nat]
  msgs,        \* [Proc -> Nat]
  tokenAt,     \* element of Proc
  tokenColor,  \* element of Color
  term         \* BOOLEAN, whether termination has been declared

vars == << active, lcolor, work, msgs, tokenAt, tokenColor, term >>

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ active = [i \in Proc |-> FALSE]
  /\ lcolor = [i \in Proc |-> 0]
  /\ work   = [i \in Proc |-> 0]
  /\ msgs   = [i \in Proc |-> 0]
  /\ tokenAt = 0
  /\ tokenColor = 0
  /\ term = FALSE

(***************************************************************************)
(* Helper predicates                                                       *)
(***************************************************************************)

AllPassive == \A i \in Proc : active[i] = FALSE

NoPending == \A i \in Proc : work[i] = 0 /\ msgs[i] = 0

AllWhite == \A i \in Proc : lcolor[i] = 0

AllPassiveNoWork == AllPassive /\ NoPending

TypeInv ==
  /\ tokenAt \in Proc
  /\ tokenColor \in Color
  /\ active \in [Proc -> BOOLEAN]
  /\ lcolor \in [Proc -> Color]
  /\ work   \in [Proc -> Nat]
  /\ msgs   \in [Proc -> Nat]
  /\ term \in BOOLEAN

LocalStateDomain == TypeInv

TokenUnique == tokenAt \in Proc

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* An active process may generate new local work.
GenerateLocal(i) ==
  /\ ~term
  /\ i \in Proc
  /\ active[i]
  /\ work' = [work EXCEPT ![i] = work[i] + 1]
  /\ UNCHANGED << active, lcolor, msgs, tokenAt, tokenColor, term >>

\* An active process may send a unit of work to a lower-indexed process j < i,
\* turning itself black (lcolor[i] := 1). This abstracts messages traveling "backward"
\* in the ring order used by the token algorithm.
SendLower(i, j) ==
  /\ ~term
  /\ i \in Proc /\ j \in Proc /\ j < i
  /\ active[i]
  /\ msgs' = [msgs EXCEPT ![j] = msgs[j] + 1]
  /\ lcolor' = [lcolor EXCEPT ![i] = 1]
  /\ UNCHANGED << active, work, tokenAt, tokenColor, term >>

\* An active process may send to a higher-indexed process j > i without changing color.
SendHigher(i, j) ==
  /\ ~term
  /\ i \in Proc /\ j \in Proc /\ j > i
  /\ active[i]
  /\ msgs' = [msgs EXCEPT ![j] = msgs[j] + 1]
  /\ UNCHANGED << active, work, lcolor, tokenAt, tokenColor, term >>

\* A process may dequeue an incoming message, converting it to local work and becoming active.
ProcessMsg(i) ==
  /\ ~term
  /\ i \in Proc
  /\ msgs[i] > 0
  /\ msgs'   = [msgs EXCEPT ![i] = msgs[i] - 1]
  /\ work'   = [work EXCEPT ![i] = work[i] + 1]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED << lcolor, tokenAt, tokenColor, term >>

\* A process executes one unit of local work. If that empties both local work and incoming messages,
\* it can become passive.
DoUnit(i) ==
  /\ ~term
  /\ i \in Proc
  /\ work[i] > 0
  /\ work' = [work EXCEPT ![i] = work[i] - 1]
  /\ active' =
       [ active EXCEPT
           ![i] = IF work[i] - 1 > 0 \/ msgs[i] > 0 THEN TRUE ELSE FALSE ]
  /\ UNCHANGED << lcolor, msgs, tokenAt, tokenColor, term >>

\* The unique token is forwarded to the next process in the ring.
\* When leaving process i != 0, the token ORs in lcolor[i]; lcolor[i] is then reset to white.
\* When leaving process 0, the token is reset to white (classic ring algorithm).
TokenPass(i) ==
  /\ ~term
  /\ i \in Proc
  /\ tokenAt = i
  /\ tokenAt' = NextProc(i)
  /\ tokenColor' = IF i = 0 THEN 0 ELSE IF tokenColor = 1 \/ lcolor[i] = 1 THEN 1 ELSE 0
  /\ lcolor' = [lcolor EXCEPT ![i] = 0]
  /\ UNCHANGED << active, work, msgs, term >>

\* Termination is declared at process 0 when the token is white at 0 and the system is globally quiescent.
Detect ==
  /\ ~term
  /\ tokenAt = 0
  /\ tokenColor = 0
  /\ AllPassiveNoWork
  /\ term' = TRUE
  /\ UNCHANGED << active, lcolor, work, msgs, tokenAt, tokenColor >>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)

Next ==
  \/ \E i \in Proc : GenerateLocal(i)
  \/ \E i \in Proc, j \in Proc : SendLower(i, j)
  \/ \E i \in Proc, j \in Proc : SendHigher(i, j)
  \/ \E i \in Proc : ProcessMsg(i)
  \/ \E i \in Proc : DoUnit(i)
  \/ \E i \in Proc : TokenPass(i)
  \/ Detect

(***************************************************************************)
(* Specification with fairness                                             *)
(***************************************************************************)

\* Scheduling and delivery fairness:
\*  - If a process continuously has a pending local unit, it will eventually execute it.
\*  - If a process continuously has incoming messages, it will eventually dequeue them.
\*  - If the token is at a process continuously, it will eventually be forwarded.
Fairness ==
  /\ \A i \in Proc : WF_vars(DoUnit(i))
  /\ \A i \in Proc : WF_vars(ProcessMsg(i))
  /\ \A i \in Proc : WF_vars(TokenPass(i))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* The token is always at a valid process and uses allowed colors.
TokenSafety ==
  [](tokenAt \in Proc /\ tokenColor \in Color)

\* No two tokens ever exist concurrently (enforced structurally by a single tokenAt).
NoTwoTokens ==
  [](TokenUnique)

\* Local states remain within allowed domains.
LocalStateSafety ==
  [](LocalStateDomain)

Safety ==
  TokenSafety /\ NoTwoTokens /\ LocalStateSafety

(***************************************************************************)
(* Liveness and correctness properties for termination detection           *)
(***************************************************************************)

\* Soundness: termination is never declared unless all processes are passive
\* and there is no pending work in any queue.
TerminationSoundness ==
  [] (term => AllPassiveNoWork)

\* Completeness/Liveness: If the system becomes and remains globally quiescent,
\* then eventually termination is declared (under fairness and token circulation).
TerminationLiveness ==
  (<>[] AllPassiveNoWork) => (<> term)

\* No false positives under ongoing work: If termination is declared, then no process is active
\* and there is no potential for immediate work (by our model, generation requires activity).
NoFalsePositive ==
  TerminationSoundness

=============================================================================