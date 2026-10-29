---- MODULE Slush ----
(***************************************************************************)
(* Specification of the Slush protocol, a simple consensus algorithm from *)
(* the Avalanche family. The model has four kinds of behaviour:           *)
(*                                                                         *)
(*  - Nodes hold a color (Red, Blue, or NoColor).                          *)
(*  - Loop processes (one per node) repeatedly query a sampled set of      *)
(*    peers and flip their color if enough peers disagree.                 *)
(*  - Query processes (one per node) answer queries with their current    *)
(*    color. An uncolored node first adopts the querier's color.          *)
(*  - A single client process assigns colors to uncolored nodes.          *)
(*                                                                         *)
(* NOTE: Slush is probabilistic in intent: sampling is random and the     *)
(* guarantees hold with high probability. This TLA+ model is NOT          *)
(* probabilistic. Sampling is pure nondeterminism, so the model is mainly *)
(* useful as executable pseudocode plus basic temporal checking, such as  *)
(* checking that all processes terminate.                                 *)
(*                                                                         *)
(* The spec is written in the style of a PlusCal translation, with a pc   *)
(* variable recording the control state of each process.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    NodeCount,            \* Number of nodes in the network
    SlushIterationCount,  \* Number of query rounds each node performs
    SampleSetSize,        \* Number of peers sampled per round (k)
    PickFlipThreshold     \* Number of disagreeing replies needed to flip (alpha)

ASSUME NodeCountAssumption ==
    NodeCount \in Nat /\ NodeCount >= 2
ASSUME IterationAssumption ==
    SlushIterationCount \in Nat
ASSUME SampleSetSizeAssumption ==
    SampleSetSize \in 1..(NodeCount - 1)
ASSUME ThresholdAssumption ==
    PickFlipThreshold \in 1..SampleSetSize

-----------------------------------------------------------------------------
Red      == "Red"
Blue     == "Blue"
Color    == {Red, Blue}
NoColor  == "NoColor"

Node == 1..NodeCount

\* Process identifiers. They are kept disjoint.
SlushQueryProcess == 1..NodeCount
SlushLoopProcess  == (NodeCount + 1)..(2 * NodeCount)
ClientProcess     == {2 * NodeCount + 1}
ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup ClientProcess

\* The node on which a query or loop process runs.
HostOf(pid) ==
    IF pid \in SlushQueryProcess THEN pid ELSE pid - NodeCount

MessageType == {"QueryMessage", "QueryReplyMessage"}

Message ==
    [src : Node, dst : Node, type : MessageType, color : Color]

OtherColor(c) == CHOOSE oc \in Color : oc # c

PossibleSampleSets(n) ==
    {s \in SUBSET (Node \ {n}) : Cardinality(s) = SampleSetSize}

-----------------------------------------------------------------------------
VARIABLES
    color,        \* color[n]: the current color of node n
    message,      \* The set of in-flight messages
    sampleSet,    \* sampleSet[p]: peers queried in the current round by loop process p
    loopVariant,  \* loopVariant[p]: number of rounds completed by loop process p
    pc            \* Control state of each process

vars == <<color, message, sampleSet, loopVariant, pc>>

QueryMessagesFor(n) ==
    {m \in message : m.type = "QueryMessage" /\ m.dst = n}

RepliesFor(n) ==
    {m \in message : m.type = "QueryReplyMessage" /\ m.dst = n}

AllLoopsDone == \A p \in SlushLoopProcess : pc[p] = "Done"

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Color \cup {NoColor}]
    /\ message \subseteq Message
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]
    /\ pc \in [ProcSet -> {"QueryReplyLoop", "WaitForMessage",
                           "RequireColorAssignment", "ExecuteSlushLoop",
                           "QuerySampleSet", "TallyQueryReplies",
                           "ClientRequestLoop", "Done"}]

-----------------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ message = {}
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopVariant = [p \in SlushLoopProcess |-> 0]
    /\ pc = [self \in ProcSet |->
                CASE self \in SlushQueryProcess -> "QueryReplyLoop"
                  [] self \in SlushLoopProcess  -> "RequireColorAssignment"
                  [] self \in ClientProcess     -> "ClientRequestLoop"]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Query process: answers queries with the node's current color.          *)
(* If the node is uncolored, it first adopts the querier's color.         *)
(***************************************************************************)
QueryReplyLoop(self) ==
    /\ pc[self] = "QueryReplyLoop"
    /\ IF AllLoopsDone
         THEN pc' = [pc EXCEPT ![self] = "Done"]
         ELSE pc' = [pc EXCEPT ![self] = "WaitForMessage"]
    /\ UNCHANGED <<color, message, sampleSet, loopVariant>>

WaitForMessage(self) ==
    LET host == HostOf(self) IN
    /\ pc[self] = "WaitForMessage"
    /\ QueryMessagesFor(host) # {} \/ AllLoopsDone
    /\ IF QueryMessagesFor(host) # {}
         THEN \E msg \in QueryMessagesFor(host) :
                LET newColor == IF color[host] = NoColor
                                  THEN msg.color
                                  ELSE color[host]
                IN /\ color' = [color EXCEPT ![host] = newColor]
                   /\ message' = (message \ {msg}) \cup
                                 {[src   |-> host,
                                   dst   |-> msg.src,
                                   type  |-> "QueryReplyMessage",
                                   color |-> newColor]}
         ELSE UNCHANGED <<color, message>>
    /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
    /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(self) == QueryReplyLoop(self) \/ WaitForMessage(self)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Loop process: waits until its node has a color, then runs              *)
(* SlushIterationCount rounds of sampling and tallying.                   *)
(***************************************************************************)
RequireColorAssignment(self) ==
    /\ pc[self] = "RequireColorAssignment"
    /\ color[HostOf(self)] # NoColor
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED <<color, message, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
    /\ pc[self] = "ExecuteSlushLoop"
    /\ IF loopVariant[self] < SlushIterationCount
         THEN pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
         ELSE pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<color, message, sampleSet, loopVariant>>

QuerySampleSet(self) ==
    LET host == HostOf(self) IN
    /\ pc[self] = "QuerySampleSet"
    /\ \E s \in PossibleSampleSets(host) :
         /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
         /\ message' = message \cup
                       {[src   |-> host,
                         dst   |-> t,
                         type  |-> "QueryMessage",
                         color |-> color[host]] : t \in s}
    /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
    /\ UNCHANGED <<color, loopVariant>>

TallyQueryReplies(self) ==
    LET host    == HostOf(self)
        replies == {m \in RepliesFor(host) : m.src \in sampleSet[self]}
        disagreeing == {m \in replies : m.color # color[host]}
    IN
    /\ pc[self] = "TallyQueryReplies"
    /\ \A s \in sampleSet[self] : \E m \in replies : m.src = s
    /\ color' = IF Cardinality(disagreeing) >= PickFlipThreshold
                  THEN [color EXCEPT ![host] = OtherColor(color[host])]
                  ELSE color
    /\ message' = message \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
    /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoop(self) ==
    \/ RequireColorAssignment(self)
    \/ ExecuteSlushLoop(self)
    \/ QuerySampleSet(self)
    \/ TallyQueryReplies(self)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Client process: assigns colors to uncolored nodes until none remain.   *)
(***************************************************************************)
ClientRequestLoop(self) ==
    /\ pc[self] = "ClientRequestLoop"
    /\ IF \E n \in Node : color[n] = NoColor
         THEN /\ \E n \in {m \in Node : color[m] = NoColor} :
                   \E c \in Color :
                      color' = [color EXCEPT ![n] = c]
              /\ pc' = [pc EXCEPT ![self] = "ClientRequestLoop"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED color
    /\ UNCHANGED <<message, sampleSet, loopVariant>>

Client(self) == ClientRequestLoop(self)

-----------------------------------------------------------------------------
\* Allow infinite stuttering once all processes are done, to avoid deadlock.
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E self \in SlushQueryProcess : SlushQuery(self)
    \/ \E self \in SlushLoopProcess  : SlushLoop(self)
    \/ \E self \in ClientProcess     : Client(self)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in SlushQueryProcess : WF_vars(SlushQuery(self))
    /\ \A self \in SlushLoopProcess  : WF_vars(SlushLoop(self))
    /\ \A self \in ClientProcess     : WF_vars(Client(self))

-----------------------------------------------------------------------------
\* Every process eventually reaches the Done control state.
Termination == <>(\A self \in ProcSet : pc[self] = "Done")

THEOREM Spec => []TypeInvariant
THEOREM Spec => Termination
=============================================================================