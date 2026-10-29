---------------------------- MODULE Slush ----------------------------
(***************************************************************************)
(* Slush: the simplest Avalanche-family consensus primitive.              *)
(* N hosts communicate asynchronously by message passing.  Each host has  *)
(* two concurrent processes:                                               *)
(*   - a querying process, which runs M rounds.  In each round it picks a *)
(*     sample of K other hosts, queries them, tallies the replies, and    *)
(*     adopts a color if at least Alpha replies match it.  After M rounds *)
(*     it broadcasts termination.                                         *)
(*   - a query (answering) process, which answers incoming queries with   *)
(*     its current color.  An uncolored host first adopts the color in    *)
(*     the query.  It stops answering once its host has terminated.       *)
(* Sampling and message delivery are nondeterministic; nothing is         *)
(* probabilistic.                                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,      \* number of hosts
    K,      \* sample size
    Alpha,  \* threshold of matching replies needed to adopt a color
    M       \* number of consensus rounds per host

ASSUME /\ N \in Nat \ {0}
       /\ K \in Nat \ {0}
       /\ K <= N - 1
       /\ Alpha \in Nat
       /\ 2 * Alpha > K
       /\ Alpha <= K
       /\ M \in Nat

Hosts   == 1..N
Red     == "Red"
Blue    == "Blue"
NoColor == "NoColor"
Colors  == {Red, Blue}
AllColors == Colors \cup {NoColor}

Opposite(c) == IF c = Red THEN Blue ELSE Red

Rounds == 0..M

QueryMsgs == [type : {"Query"}, src : Hosts, dst : Hosts,
              color : Colors, rnd : Rounds]
ReplyMsgs == [type : {"Reply"}, src : Hosts, dst : Hosts,
              color : Colors, rnd : Rounds]
Messages == QueryMsgs \cup ReplyMsgs

VARIABLES
    color,        \* color[h] : current preferred color of host h
    round,        \* round[h] : number of completed rounds of host h
    pc,           \* pc[h]    : control state of h's querying process
    sample,       \* sample[h]: current sample set of host h
    messages,     \* set of messages in flight
    terminated,   \* set of hosts that have broadcast termination
    sentQueries   \* history: <<src, dst, rnd>> of every query ever sent

vars == <<color, round, pc, sample, messages, terminated, sentQueries>>

PCStates == {"loop", "wait", "done"}

---------------------------------------------------------------------------
Init ==
    /\ color \in [Hosts -> AllColors]
    /\ round = [h \in Hosts |-> 0]
    /\ pc = [h \in Hosts |-> "loop"]
    /\ sample = [h \in Hosts |-> {}]
    /\ messages = {}
    /\ terminated = {}
    /\ sentQueries = {}

---------------------------------------------------------------------------
(* A client gives an initial color to an uncolored host. *)
ClientColor(h) ==
    /\ color[h] = NoColor
    /\ h \notin terminated
    /\ \E c \in Colors : color' = [color EXCEPT ![h] = c]
    /\ UNCHANGED <<round, pc, sample, messages, terminated, sentQueries>>

(* Querying process: choose a sample of K distinct other hosts and query them. *)
StartRound(h) ==
    /\ pc[h] = "loop"
    /\ color[h] # NoColor
    /\ round[h] < M
    /\ \E S \in SUBSET (Hosts \ {h}) :
         /\ Cardinality(S) = K
         /\ sample' = [sample EXCEPT ![h] = S]
         /\ messages' = messages \cup
               { [type |-> "Query", src |-> h, dst |-> d,
                  color |-> color[h], rnd |-> round[h]] : d \in S }
         /\ sentQueries' = sentQueries \cup { <<h, d, round[h]>> : d \in S }
    /\ pc' = [pc EXCEPT ![h] = "wait"]
    /\ UNCHANGED <<color, round, terminated>>

RepliesFor(h) ==
    { m \in messages : /\ m.type = "Reply"
                       /\ m.dst = h
                       /\ m.rnd = round[h] }

HasReply(h, d) == \E m \in RepliesFor(h) : m.src = d

Tally(h, c) == Cardinality({ m \in RepliesFor(h) : m.color = c })

(* Querying process: once every sampled host has replied (or has terminated *)
(* and will never reply), count the replies and apply the threshold rule.   *)
(* Processed replies and any unanswered queries of this round are removed.  *)
TallyRound(h) ==
    /\ pc[h] = "wait"
    /\ \A d \in sample[h] : HasReply(h, d) \/ d \in terminated
    /\ color' = [color EXCEPT ![h] =
                    IF \E c \in Colors : Tally(h, c) >= Alpha
                    THEN CHOOSE c \in Colors : Tally(h, c) >= Alpha
                    ELSE color[h]]
    /\ messages' = (messages \ RepliesFor(h))
                     \ { m \in messages : /\ m.type = "Query"
                                          /\ m.src = h
                                          /\ m.rnd = round[h] }
    /\ round' = [round EXCEPT ![h] = round[h] + 1]
    /\ sample' = [sample EXCEPT ![h] = {}]
    /\ pc' = [pc EXCEPT ![h] = "loop"]
    /\ UNCHANGED <<terminated, sentQueries>>

(* Querying process: after M rounds, broadcast termination. *)
Terminate(h) ==
    /\ pc[h] = "loop"
    /\ color[h] # NoColor
    /\ round[h] = M
    /\ pc' = [pc EXCEPT ![h] = "done"]
    /\ terminated' = terminated \cup {h}
    /\ UNCHANGED <<color, round, sample, messages, sentQueries>>

(* Query (answering) process: answer a pending query with the current color. *)
(* An uncolored host adopts the querier's color first.                       *)
Respond(h) ==
    /\ h \notin terminated
    /\ \E m \in messages :
         /\ m.type = "Query"
         /\ m.dst = h
         /\ LET newColor == IF color[h] = NoColor THEN m.color ELSE color[h]
            IN  /\ color' = [color EXCEPT ![h] = newColor]
                /\ messages' = (messages \ {m}) \cup
                     { [type |-> "Reply", src |-> h, dst |-> m.src,
                        color |-> newColor, rnd |-> m.rnd] }
    /\ UNCHANGED <<round, pc, sample, terminated, sentQueries>>

AllTerminated == terminated = Hosts

Finished == AllTerminated /\ UNCHANGED vars

Next ==
    \/ \E h \in Hosts :
         \/ ClientColor(h)
         \/ StartRound(h)
         \/ TallyRound(h)
         \/ Terminate(h)
         \/ Respond(h)
    \/ Finished

Fairness ==
    \A h \in Hosts :
        /\ WF_vars(StartRound(h))
        /\ WF_vars(TallyRound(h))
        /\ WF_vars(Terminate(h))
        /\ WF_vars(Respond(h))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Invariants *)

ColorDomain == color \in [Hosts -> AllColors]

TypeOK ==
    /\ ColorDomain
    /\ round \in [Hosts -> Rounds]
    /\ pc \in [Hosts -> PCStates]
    /\ sample \in [Hosts -> SUBSET Hosts]
    /\ messages \subseteq Messages
    /\ terminated \subseteq Hosts
    /\ sentQueries \subseteq (Hosts \X Hosts \X Rounds)

MessageTyping ==
    \A m \in messages :
        /\ m \in Messages
        /\ m.src # m.dst

SampleSizeOK ==
    \A h \in Hosts :
        /\ h \notin sample[h]
        /\ (pc[h] = "wait") => Cardinality(sample[h]) = K
        /\ (pc[h] # "wait") => sample[h] = {}

QueriesToDistinctOthers ==
    \A m \in messages :
        m.type = "Query" =>
            /\ m.dst # m.src
            /\ pc[m.src] = "wait"
            /\ m.rnd = round[m.src]
            /\ m.dst \in sample[m.src]

NoMessageCorruption ==
    \A m \in messages :
        m.type = "Reply" => <<m.dst, m.src, m.rnd>> \in sentQueries

TerminatedAreDone ==
    \A h \in terminated : pc[h] = "done" /\ round[h] = M /\ color[h] \in Colors

---------------------------------------------------------------------------
(* Safety: consensus is absorbing.  Once all non-terminated hosts prefer c *)
(* (and no message in flight carries the opposite color), no host that is  *)
(* still running ever adopts the opposite color.                           *)

Consensus(c) ==
    /\ \A h \in Hosts \ terminated : color[h] = c
    /\ \A m \in messages : m.color = c

ConsensusAbsorbing ==
    \A c \in Colors : [](Consensus(c) => []Consensus(c))

ConsensusAbsorbingStep ==
    [][ \A c \in Colors :
          Consensus(c) =>
             \A h \in Hosts : (color[h] = c) => (color'[h] # Opposite(c)) ]_vars

(* Agreement: if all hosts terminate, they agree on a single color. *)
Agreement ==
    [](AllTerminated => \E c \in Colors : \A h \in Hosts : color[h] = c)

(* Termination liveness: every colored host completes its M rounds and *)
(* enters termination.                                                  *)
TerminationLiveness ==
    \A h \in Hosts :
        (color[h] # NoColor) ~> (h \in terminated /\ round[h] = M)

InitiallyColoredTerminate ==
    \A h \in Hosts :
        (color[h] # NoColor) => <>(h \in terminated /\ round[h] = M)

THEOREM Spec => [](TypeOK /\ MessageTyping /\ SampleSizeOK
                   /\ QueriesToDistinctOthers /\ NoMessageCorruption
                   /\ TerminatedAreDone)
THEOREM Spec => ConsensusAbsorbing /\ ConsensusAbsorbingStep
THEOREM Spec => TerminationLiveness /\ InitiallyColoredTerminate
=============================================================================