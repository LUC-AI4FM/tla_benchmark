------------------------------- MODULE Slush --------------------------------
(***************************************************************************)
(* Specification of the Slush protocol, a simple probabilistic consensus   *)
(* algorithm from the Avalanche family. Nodes try to agree on a color      *)
(* (Red or Blue) by repeatedly sampling peers and flipping their own       *)
(* preference when enough sampled peers prefer the other color.            *)
(*                                                                         *)
(* Each node hosts two processes:                                          *)
(*   - a SlushLoop process, which drives consensus, and                    *)
(*   - a SlushQuery process, which answers queries from other nodes.       *)
(* A ClientRequest process non-deterministically assigns initial colors    *)
(* to nodes that have none.                                                *)
(*                                                                         *)
(* NOTE: TLA+ cannot express the probabilistic convergence questions that  *)
(* are central to analyzing Slush. This spec only captures safety-style    *)
(* typing properties and termination of the processes.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,                   \* The set of nodes
    SlushLoopProcess,       \* The set of SlushLoop process identifiers
    SlushQueryProcess,      \* The set of SlushQuery process identifiers
    HostOf,                 \* Maps each loop/query process to its host node
    SlushIterationCount,    \* Number of iterations each SlushLoop executes
    SampleSetSize,          \* Number of peers sampled per iteration
    PickFlipThreshold       \* Replies needed for one color to flip pick

ClientRequestId == "ClientRequest"

ASSUME SlushLoopProcess \cap SlushQueryProcess = {}
ASSUME ClientRequestId \notin (SlushLoopProcess \cup SlushQueryProcess)
ASSUME HostOf \in [SlushLoopProcess \cup SlushQueryProcess -> Node]
ASSUME \A n \in Node :
          /\ \E p \in SlushLoopProcess : HostOf[p] = n
          /\ \E q \in SlushQueryProcess : HostOf[q] = n
ASSUME SlushIterationCount \in Nat
ASSUME SampleSetSize \in Nat \ {0}
ASSUME PickFlipThreshold \in Nat \ {0}
ASSUME PickFlipThreshold <= SampleSetSize
ASSUME \A n \in Node : SampleSetSize <= Cardinality(Node \ {n})

Red   == "Red"
Blue  == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c : c \notin Color

QueryMessageType      == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"

QueryMessage ==
    [src : Node, dst : Node, type : {QueryMessageType}, color : Color]

QueryReplyMessage ==
    [src : Node, dst : Node, type : {QueryReplyMessageType}, color : Color]

Message == QueryMessage \cup QueryReplyMessage

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {ClientRequestId}

VARIABLES
    pick,         \* Current color pick of each node
    message,      \* Set of messages in transit
    sampleSet,    \* Process-local sample set of each SlushLoop process
    loopVariant,  \* Iteration counter of each SlushLoop process
    pc            \* Program counter of each process

vars == <<pick, message, sampleSet, loopVariant, pc>>

-----------------------------------------------------------------------------

Init ==
    /\ pick = [n \in Node |-> NoColor]
    /\ message = {}
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopVariant = [p \in SlushLoopProcess |-> 0]
    /\ pc = [p \in ProcSet |->
                IF p \in SlushLoopProcess THEN "RequireColorAssignment"
                ELSE IF p \in SlushQueryProcess THEN "WaitForQueryMessageOrTermination"
                ELSE "ClientRequestLoop"]

-----------------------------------------------------------------------------
(* ClientRequest process                                                   *)
-----------------------------------------------------------------------------

ClientRequestLoop ==
    /\ pc[ClientRequestId] = "ClientRequestLoop"
    /\ IF \E n \in Node : pick[n] = NoColor
         THEN /\ \E n \in Node, c \in Color :
                    pick' = IF pick[n] = NoColor
                              THEN [pick EXCEPT ![n] = c]
                              ELSE pick
              /\ pc' = pc
         ELSE /\ pc' = [pc EXCEPT ![ClientRequestId] = "Done"]
              /\ pick' = pick
    /\ UNCHANGED <<message, sampleSet, loopVariant>>

ClientRequest == ClientRequestLoop

-----------------------------------------------------------------------------
(* SlushQuery process                                                      *)
-----------------------------------------------------------------------------

PendingQueries(host) ==
    {m \in message : m.type = QueryMessageType /\ m.dst = host}

WaitForQueryMessageOrTermination(self) ==
    /\ pc[self] = "WaitForQueryMessageOrTermination"
    /\ \/ PendingQueries(HostOf[self]) # {}
       \/ \A p \in SlushLoopProcess : pc[p] = "Done"
    /\ IF \A p \in SlushLoopProcess : pc[p] = "Done"
         THEN pc' = [pc EXCEPT ![self] = "Done"]
         ELSE pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

RespondToQueryMessage(self) ==
    LET host == HostOf[self] IN
    /\ pc[self] = "RespondToQueryMessage"
    /\ \E msg \in PendingQueries(host) :
         LET newPick == IF pick[host] = NoColor THEN msg.color ELSE pick[host]
         IN  /\ pick' = [pick EXCEPT ![host] = newPick]
             /\ message' = (message \ {msg}) \cup
                    {[src   |-> host,
                      dst   |-> msg.src,
                      type  |-> QueryReplyMessageType,
                      color |-> newPick]}
    /\ pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
    /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(self) ==
    \/ WaitForQueryMessageOrTermination(self)
    \/ RespondToQueryMessage(self)

-----------------------------------------------------------------------------
(* SlushLoop process                                                       *)
-----------------------------------------------------------------------------

RequireColorAssignment(self) ==
    /\ pc[self] = "RequireColorAssignment"
    /\ pick[HostOf[self]] # NoColor
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
    LET host == HostOf[self] IN
    /\ pc[self] = "ExecuteSlushLoop"
    /\ IF loopVariant[self] < SlushIterationCount
         THEN /\ \E s \in {ss \in SUBSET (Node \ {host}) :
                               Cardinality(ss) = SampleSetSize} :
                    /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
                    /\ message' = message \cup
                         {[src   |-> host,
                           dst   |-> peer,
                           type  |-> QueryMessageType,
                           color |-> pick[host]] : peer \in s}
              /\ loopVariant' = [loopVariant EXCEPT ![self] = @ + 1]
              /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED <<message, sampleSet, loopVariant>>
    /\ UNCHANGED pick

RepliesTo(self) ==
    {m \in message : /\ m.type = QueryReplyMessageType
                     /\ m.dst = HostOf[self]
                     /\ m.src \in sampleSet[self]}

TallyQueryReplies(self) ==
    LET host    == HostOf[self]
        replies == RepliesTo(self)
        redCount  == Cardinality({m \in replies : m.color = Red})
        blueCount == Cardinality({m \in replies : m.color = Blue})
    IN
    /\ pc[self] = "TallyQueryReplies"
    /\ \A peer \in sampleSet[self] : \E m \in replies : m.src = peer
    /\ pick' = IF redCount >= PickFlipThreshold
                 THEN [pick EXCEPT ![host] = Red]
                 ELSE IF blueCount >= PickFlipThreshold
                   THEN [pick EXCEPT ![host] = Blue]
                   ELSE pick
    /\ message' = message \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED loopVariant

SlushLoop(self) ==
    \/ RequireColorAssignment(self)
    \/ ExecuteSlushLoop(self)
    \/ TallyQueryReplies(self)

-----------------------------------------------------------------------------

\* Allows infinite stuttering once all processes are done, avoiding deadlock.
Terminating ==
    /\ \A p \in ProcSet : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ClientRequest
    \/ \E self \in SlushLoopProcess : SlushLoop(self)
    \/ \E self \in SlushQueryProcess : SlushQuery(self)
    \/ Terminating

\* No fairness conditions are specified.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------

TypeInvariant ==
    /\ pick \in [Node -> Color \cup {NoColor}]
    /\ message \subseteq Message

Termination == <>(\A p \in ProcSet : pc[p] = "Done")

\* TLA+ cannot express the probabilistic convergence properties central to
\* the analysis of Slush (e.g., "all nodes agree with high probability").

=============================================================================