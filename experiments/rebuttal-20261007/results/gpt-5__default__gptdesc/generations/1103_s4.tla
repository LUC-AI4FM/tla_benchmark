----------------------------- MODULE NBAC -----------------------------

EXTENDS Naturals, FiniteSets, TLC

(*
  Non-Blocking Atomic Commitment (NBAC) with crash failures and a
  nondeterministic local failure detector (after Raynal, 1997).

  Processes vote YES or NO, broadcast their vote, receive messages,
  may crash, and locally observe a failure detector that can change
  arbitrarily at each local step.
*)

CONSTANTS
  Proc,   \* nonempty set of process identifiers
  Votes   \* function mapping each process to its initial vote

ASSUME
  /\ Proc # {}
  /\ Votes \in [Proc -> {"YES","NO"}]

(*
  Basic domains
*)
Vals == {"YES","NO"}
Decisions == {"Undecided","Commit","Abort"}

(*
  Messages are records with a sender, a receiver, and the vote value.
*)
MsgSet == [from: Proc, to: Proc, val: Vals]

(*
  State variables
*)
VARIABLES
  crashed,   \* subset of Proc that have crashed
  net,       \* set of undelivered messages (subset of MsgSet)
  recvYes,   \* function Proc -> SUBSET Proc: YES-senders received by each proc
  recvNo,    \* function Proc -> SUBSET Proc: NO-senders received by each proc
  fd,        \* function Proc -> SUBSET Proc: processes locally suspected crashed
  decision   \* function Proc -> Decisions: local decision state

vars == << crashed, net, recvYes, recvNo, fd, decision >>

(*
  Convenience predicates
*)
AllYes == \A p \in Proc: Votes[p] = "YES"

SomeCommitted == \E p \in Proc: decision[p] = "Commit"

(*
  Initialization:
  - No one is crashed.
  - The network initially contains one vote message from every sender to every receiver.
  - No messages have been received yet.
  - Failure detectors initially suspect nobody.
  - All processes are initially undecided.
*)
Init ==
  /\ crashed = {}
  /\ net = { [from |-> p, to |-> q, val |-> Votes[p]] : p \in Proc, q \in Proc }
  /\ recvYes = [p \in Proc |-> {}]
  /\ recvNo  = [p \in Proc |-> {}]
  /\ fd      = [p \in Proc |-> {}]
  /\ decision = [p \in Proc |-> "Undecided"]

(*
  Type correctness invariant (state predicate)
*)
TypeOK ==
  /\ crashed \subseteq Proc
  /\ net \subseteq MsgSet
  /\ recvYes \in [Proc -> SUBSET Proc]
  /\ recvNo  \in [Proc -> SUBSET Proc]
  /\ fd      \in [Proc -> SUBSET Proc]
  /\ decision \in [Proc -> Decisions]

(*
  Message delivery + local FD update + local transition for process p:
  - If there is a message addressed to p, deliver exactly one such message.
  - Update p's local failure detector arbitrarily.
  - Update p's local decision according to NBAC rules:
      * If p has seen any NO, decide Abort.
      * Else if for all processes q, p has either received YES from q or suspects q,
        decide Commit.
      * Else remain Undecided.
*)
DeliverStep(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ \E m \in net:
        /\ m.to = p
        /\ \E S \in SUBSET Proc:
            /\ net' = net \ {m}
            /\ recvYes' =
                 [recvYes EXCEPT ![p] =
                    IF m.val = "YES" THEN @ \cup {m.from} ELSE @]
            /\ recvNo'  =
                 [recvNo EXCEPT ![p] =
                    IF m.val = "NO" THEN @ \cup {m.from} ELSE @]
            /\ fd' = [fd EXCEPT ![p] = S]
            /\ decision' =
                 [decision EXCEPT
                   ![p] =
                     IF @ # "Undecided" THEN @
                     ELSE IF recvNo'[p] # {} THEN "Abort"
                     ELSE IF Proc \subseteq (recvYes'[p] \cup fd'[p]) THEN "Commit"
                     ELSE "Undecided"]
            /\ UNCHANGED crashed

(*
  Local FD update + local transition for p without delivering a message.
*)
StepSilent(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ \E S \in SUBSET Proc:
      /\ net' = net
      /\ recvYes' = recvYes
      /\ recvNo' = recvNo
      /\ fd' = [fd EXCEPT ![p] = S]
      /\ decision' =
           [decision EXCEPT
             ![p] =
               IF @ # "Undecided" THEN @
               ELSE IF recvNo'[p] # {} THEN "Abort"
               ELSE IF Proc \subseteq (recvYes'[p] \cup fd'[p]) THEN "Commit"
               ELSE "Undecided"]
      /\ UNCHANGED crashed

ProcStep(p) == DeliverStep(p) \/ StepSilent(p)

(*
  Crash transition for process p.
*)
Crash(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED << net, recvYes, recvNo, fd, decision >>

(*
  Global next-state relation: one process step or one crash per transition.
*)
Next ==
  \E p \in Proc: ProcStep(p) \/ Crash(p)

(*
  Fairness: each non-crashed process takes infinitely many local steps,
  i.e., its combined per-process step (delivery + FD update + local transition)
  is weakly fair.
*)
Fairness == \A p \in Proc: WF_vars(ProcStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Additional structural safety properties and liveness conditions
*)

(*
  Messages and receive buffers are well-typed and consistent with Votes.
*)
MsgWellTyped ==
  /\ \A m \in net: m \in MsgSet
  /\ \A p \in Proc: recvYes[p] \subseteq { q \in Proc: Votes[q] = "YES" }
  /\ \A p \in Proc: recvNo[p]  \subseteq { q \in Proc: Votes[q] = "NO" }
  /\ \A p \in Proc: recvYes[p] \cap recvNo[p] = {}

(*
  Agreement: no two processes decide differently.
*)
Agreement ==
  \A p, q \in Proc:
    /\ decision[p] \in {"Commit","Abort"}
    /\ decision[q] \in {"Commit","Abort"}
    => decision[p] = decision[q]

(*
  Validity (safety):
  - Commit requires that all initial votes are YES.
  - If any process voted NO, then no process may decide COMMIT.
*)
CommitRequiresAllYes ==
  (\E p \in Proc: decision[p] = "Commit") => AllYes

ForbidCommitIfAnyNo ==
  (\E q \in Proc: Votes[q] = "NO") => \A p \in Proc: decision[p] # "Commit"

(*
  Validity relating unanimous YES votes to commit outcomes (liveness):
  If all processes voted YES, then eventually some process may (will, under this spec)
  decide COMMIT.
*)
UnanimousYesPossibleCommit ==
  AllYes => <> SomeCommitted

=======================================================================