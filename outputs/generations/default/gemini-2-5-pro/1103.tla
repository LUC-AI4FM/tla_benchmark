-------------------------- MODULE NBAC --------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Proc
CONSTANT InitialVote
ASSUME /\ IsFiniteSet(Proc)
       /\ Proc /= {}
       /\ InitialVote \in [Proc -> {"YES", "NO"}]

VoteValue == {"YES", "NO"}
DecisionValue == {"COMMIT", "ABORT", "UNDECIDED"}
PCValue == {"VOTING", "WAITING", "DECIDED"}

VARIABLES pc, decision, crashed, suspected, messages

vars == <<pc, decision, crashed, suspected, messages>>

Message == [to: Proc, from: Proc, type: "VOTE", val: VoteValue]

TypeOK ==
    /\ pc \in [Proc -> PCValue]
    /\ decision \in [Proc -> DecisionValue]
    /\ crashed \subseteq Proc
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ messages \subseteq Message

Init ==
    /\ pc = [p \in Proc |-> "VOTING"]
    /\ decision = [p \in Proc |-> "UNDECIDED"]
    /\ crashed = {}
    /\ suspected = [p \in Proc |-> {}]
    /\ messages = {}

\* A process p that has not yet crashed may crash.
Crash(p) ==
    /\ p \in Proc \ crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<pc, decision, suspected, messages>>

\* The local failure detector of a non-crashed process p may non-deterministically
\* update its set of suspected processes.
UpdateSuspicions(p) ==
    /\ p \in Proc \ crashed
    /\ \E new_suspected \subseteq Proc \ {p} :
        suspected' = [suspected EXCEPT ![p] = new_suspected]
    /\ UNCHANGED <<pc, decision, crashed, messages>>

\* A non-crashed process p in the VOTING state broadcasts its vote.
SendVote(p) ==
    /\ p \in Proc \ crashed
    /\ pc[p] = "VOTING"
    /\ messages' = messages \cup { [to |-> q, from |-> p, type |-> "VOTE", val |-> InitialVote[p]] : q \in Proc }
    /\ pc' = [pc EXCEPT ![p] = "WAITING"]
    /\ UNCHANGED <<decision, crashed, suspected>>

\* A non-crashed process p in the WAITING state attempts to make a decision.
Decide(p) ==
    /\ p \in Proc \ crashed
    /\ pc[p] = "WAITING"
    /\ LET
        p_messages == {m \in messages : m.to = p}
        no_voters == {m.from : m \in p_messages | m.val = "NO"}
        yes_voters == {m.from : m \in p_messages | m.val = "YES"}
       IN
        \/ (* Decide ABORT if a "NO" vote is received *)
           /\ no_voters /= {}
           /\ decision' = [decision EXCEPT ![p] = "ABORT"]
           /\ pc' = [pc EXCEPT ![p] = "DECIDED"]
           /\ UNCHANGED <<crashed, suspected, messages>>
        \/ (* Decide COMMIT if "YES" is received from all non-suspected processes and no "NO" is received *)
           /\ no_voters = {}
           /\ (Proc \ suspected[p]) \subseteq yes_voters
           /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
           /\ pc' = [pc EXCEPT ![p] = "DECIDED"]
           /\ UNCHANGED <<crashed, suspected, messages>>

\* The next-state relation is the disjunction of all possible actions.
Next ==
    \/ \E p \in Proc : Crash(p)
    \/ \E p \in Proc : UpdateSuspicions(p)
    \/ \E p \in Proc : SendVote(p)
    \/ \E p \in Proc : Decide(p)

\* The full specification, allowing stuttering steps.
Spec == Init /\ [][Next]_vars

=============================================================================