------------------------------- MODULE Slush -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,                 \* the set of hosts
    SlushLoopProcess,     \* querying processes, one per host
    SlushQueryProcess,    \* answering processes, one per host
    HostMapping,          \* function: Node -> set of process ids running on it
    SlushIterationCount,  \* number of rounds each host executes
    SampleSetSize,        \* k: cardinality of each sample
    PickFlipThreshold     \* alpha: replies needed to adopt a color

ASSUME SlushIterationCount \in Nat
ASSUME SampleSetSize \in Nat
ASSUME PickFlipThreshold \in Nat

Red   == "Red"
Blue  == "Blue"
Color == {Red, Blue}

NoColor   == "NoColor"
NoMessage == "NoMessage"

QueryMessageType       == "QueryMessageType"
QueryReplyMessageType  == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"

Process == SlushLoopProcess \cup SlushQueryProcess

HostOf(pid) == CHOOSE n \in Node : pid \in HostMapping[n]
LoopProcessOf(n)  == CHOOSE p \in SlushLoopProcess  : p \in HostMapping[n]
QueryProcessOf(n) == CHOOSE p \in SlushQueryProcess : p \in HostMapping[n]

QueryMessage ==
    [type : {QueryMessageType}, src : SlushLoopProcess,
     dst : SlushQueryProcess, color : Color]
QueryReplyMessage ==
    [type : {QueryReplyMessageType}, src : SlushQueryProcess,
     dst : SlushLoopProcess, color : Color]
TerminationMessage ==
    [type : {TerminationMessageType}, src : SlushLoopProcess,
     dst : SlushQueryProcess, color : {NoColor}]
Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage

LoopLabels  == {"RequireColorAssignment", "ExecuteSlushLoop", "QuerySampleSet",
                "TallyQueryReplies", "SlushLoopTermination", "Done"}
QueryLabels == {"QueryReplyLoop", "Done"}

VARIABLES
    color,      \* preferred color of each host
    message,    \* messages in flight
    pc,         \* program counter of each process
    iteration,  \* completed rounds of each loop process
    sampleSet,  \* current sample of each loop process
    lastQuery   \* last query handled by each query process

vars == <<color, message, pc, iteration, sampleSet, lastQuery>>

-----------------------------------------------------------------------------
Init ==
    /\ color     = [n \in Node |-> NoColor]
    /\ message   = {}
    /\ pc        = [p \in Process |->
                      IF p \in SlushLoopProcess THEN "RequireColorAssignment"
                                                ELSE "QueryReplyLoop"]
    /\ iteration = [p \in SlushLoopProcess |-> 0]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ lastQuery = [p \in SlushQueryProcess |-> NoMessage]

\* A client assigns an initial color to an uncolored host.
ClientRequest(n) ==
    /\ color[n] = NoColor
    /\ \E c \in Color : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<message, pc, iteration, sampleSet, lastQuery>>

-----------------------------------------------------------------------------
\* Loop (querying) process actions

RequireColorAssignment(self) ==
    /\ pc[self] = "RequireColorAssignment"
    /\ color[HostOf(self)] # NoColor
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED <<color, message, iteration, sampleSet, lastQuery>>

ExecuteSlushLoop(self) ==
    /\ pc[self] = "ExecuteSlushLoop"
    /\ pc' = [pc EXCEPT ![self] =
                IF iteration[self] < SlushIterationCount
                THEN "QuerySampleSet" ELSE "SlushLoopTermination"]
    /\ UNCHANGED <<color, message, iteration, sampleSet, lastQuery>>

QuerySampleSet(self) ==
    /\ pc[self] = "QuerySampleSet"
    /\ \E s \in SUBSET (Node \ {HostOf(self)}) :
          /\ Cardinality(s) = SampleSetSize
          /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
          /\ message' = message \cup
                { [type  |-> QueryMessageType,
                   src   |-> self,
                   dst   |-> QueryProcessOf(n),
                   color |-> color[HostOf(self)]] : n \in s }
    /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
    /\ UNCHANGED <<color, iteration, lastQuery>>

RepliesTo(self) ==
    {m \in message : m.type = QueryReplyMessageType /\ m.dst = self}

TallyQueryReplies(self) ==
    /\ pc[self] = "TallyQueryReplies"
    /\ LET replies == RepliesTo(self)
           candidates == {c \in Color :
                Cardinality({m \in replies : m.color = c}) >= PickFlipThreshold}
       IN  /\ Cardinality(replies) = SampleSetSize
           /\ color' = [color EXCEPT ![HostOf(self)] =
                          IF candidates = {} THEN @
                          ELSE IF @ \in candidates THEN @
                          ELSE CHOOSE c \in candidates : TRUE]
           /\ message' = message \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
    /\ iteration' = [iteration EXCEPT ![self] = @ + 1]
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED lastQuery

SlushLoopTermination(self) ==
    /\ pc[self] = "SlushLoopTermination"
    /\ message' = message \cup
          { [type |-> TerminationMessageType, src |-> self,
             dst |-> q, color |-> NoColor] : q \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<color, iteration, sampleSet, lastQuery>>

LoopStep(self) ==
    \/ RequireColorAssignment(self)
    \/ ExecuteSlushLoop(self)
    \/ QuerySampleSet(self)
    \/ TallyQueryReplies(self)
    \/ SlushLoopTermination(self)

-----------------------------------------------------------------------------
\* Query (answering) process actions

AnswerQuery(self) ==
    /\ pc[self] = "QueryReplyLoop"
    /\ \E m \in message :
          /\ m.type = QueryMessageType
          /\ m.dst = self
          /\ LET h == HostOf(self)
                 newColor == IF color[h] = NoColor THEN m.color ELSE color[h]
             IN  /\ color' = [color EXCEPT ![h] = newColor]
                 /\ message' = (message \ {m}) \cup
                       { [type  |-> QueryReplyMessageType,
                          src   |-> self,
                          dst   |-> m.src,
                          color |-> newColor] }
          /\ lastQuery' = [lastQuery EXCEPT ![self] = m]
    /\ UNCHANGED <<pc, iteration, sampleSet>>

TerminationMessagesTo(self) ==
    { [type |-> TerminationMessageType, src |-> l,
       dst |-> self, color |-> NoColor] : l \in SlushLoopProcess }

QueryTerminate(self) ==
    /\ pc[self] = "QueryReplyLoop"
    /\ TerminationMessagesTo(self) \subseteq message
    /\ message' = message \ TerminationMessagesTo(self)
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<color, iteration, sampleSet, lastQuery>>

QueryStep(self) == AnswerQuery(self) \/ QueryTerminate(self)

-----------------------------------------------------------------------------
Terminating ==
    /\ \A p \in Process : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node : ClientRequest(n)
    \/ \E p \in SlushLoopProcess : LoopStep(p)
    \/ \E p \in SlushQueryProcess : QueryStep(p)
    \/ Terminating

Fairness ==
    /\ \A p \in SlushLoopProcess  : WF_vars(LoopStep(p))
    /\ \A p \in SlushQueryProcess : WF_vars(QueryStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Invariants

TypeInvariant ==
    /\ color     \in [Node -> Color \cup {NoColor}]
    /\ message   \subseteq Message
    /\ pc        \in [Process -> LoopLabels \cup QueryLabels]
    /\ \A p \in SlushLoopProcess  : pc[p] \in LoopLabels
    /\ \A p \in SlushQueryProcess : pc[p] \in QueryLabels
    /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ lastQuery \in [SlushQueryProcess -> Message \cup {NoMessage}]

ColorDomainInvariant ==
    \A n \in Node : color[n] \in Color \cup {NoColor}

MessageTypeInvariant ==
    \A m \in message : m \in Message

SampleSetSizeInvariant ==
    \A p \in SlushLoopProcess :
        IF pc[p] = "TallyQueryReplies"
        THEN Cardinality(sampleSet[p]) = SampleSetSize
        ELSE sampleSet[p] = {}

QueriesToDistinctOtherHosts ==
    /\ \A p \in SlushLoopProcess : HostOf(p) \notin sampleSet[p]
    /\ \A m \in message :
          m.type = QueryMessageType => HostOf(m.dst) # HostOf(m.src)
    /\ \A m1, m2 \in message :
          (/\ m1.type = QueryMessageType /\ m2.type = QueryMessageType
           /\ m1.src = m2.src /\ m1 # m2) => m1.dst # m2.dst

\* No message corruption: every query/reply belongs to an outstanding round.
NoSpuriousMessages ==
    \A m \in message :
        /\ m.type = QueryMessageType =>
              /\ pc[m.src] = "TallyQueryReplies"
              /\ HostOf(m.dst) \in sampleSet[m.src]
        /\ m.type = QueryReplyMessageType =>
              /\ pc[m.dst] = "TallyQueryReplies"
              /\ HostOf(m.src) \in sampleSet[m.dst]
              /\ ~\E q \in message :
                    q.type = QueryMessageType /\ q.src = m.dst /\ q.dst = m.src

-----------------------------------------------------------------------------
\* Properties

Consensus(c) ==
    /\ \A n \in Node : color[n] = c
    /\ \A m \in message :
          m.type \in {QueryMessageType, QueryReplyMessageType} => m.color = c

ConsensusAbsorbing ==
    [][\A c \in Color : Consensus(c) => Consensus(c)']_vars

Safety == \A c \in Color : [](Consensus(c) => []Consensus(c))

AllTerminated == \A p \in SlushLoopProcess : pc[p] = "Done"

Agreement ==
    AllTerminated => \E c \in Color : \A n \in Node : color[n] = c

EventualAgreement == <>[](AllTerminated => Agreement)

Termination ==
    \A p \in SlushLoopProcess :
        (color[HostOf(p)] # NoColor) ~> (pc[p] = "Done")

RoundsCompleted ==
    \A p \in SlushLoopProcess :
        pc[p] = "Done" => iteration[p] = SlushIterationCount

=============================================================================