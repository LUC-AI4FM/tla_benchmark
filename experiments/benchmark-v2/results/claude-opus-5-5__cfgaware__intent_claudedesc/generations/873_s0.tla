------------------------------- MODULE Slush -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,
    SlushLoopProcess,
    SlushQueryProcess,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold

ASSUME
    /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
    /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
    /\ SlushLoopProcess \cap SlushQueryProcess = {}
    /\ SlushIterationCount \in Nat
    /\ SampleSetSize \in Nat
    /\ SampleSetSize < Cardinality(Node)
    /\ PickFlipThreshold \in Nat
    /\ PickFlipThreshold <= SampleSetSize

(***************************************************************************)
(* Map each loop process and each query process to the node hosting it.   *)
(* Every node hosts exactly one loop process and one query process.       *)
(***************************************************************************)
LoopHost ==
    CHOOSE f \in [SlushLoopProcess -> Node] :
        \A n \in Node : \E p \in SlushLoopProcess : f[p] = n

QueryHost ==
    CHOOSE f \in [SlushQueryProcess -> Node] :
        \A n \in Node : \E p \in SlushQueryProcess : f[p] = n

HostMapping ==
    [p \in SlushLoopProcess \cup SlushQueryProcess |->
        IF p \in SlushLoopProcess THEN LoopHost[p] ELSE QueryHost[p]]

LoopProcessOf(n) == CHOOSE p \in SlushLoopProcess : HostMapping[p] = n

Red  == "Red"
Blue == "Blue"
Color == {Red, Blue}

NoColor == CHOOSE c : c \notin Color

QueryMessageType      == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"

QueryMessage ==
    [type : {QueryMessageType}, src : Node, dst : Node, color : Color]

QueryReplyMessage ==
    [type : {QueryReplyMessageType}, src : Node, dst : Node, color : Color]

Message == QueryMessage \cup QueryReplyMessage

NoMessage == CHOOSE m : m \notin Message

VARIABLES
    pick,         \* current color of each node
    message,      \* set of in-flight messages
    pc,           \* program counter of each process
    sampleSet,    \* current sample of each loop process
    loopVariant   \* number of iterations completed by each loop process

vars == <<pick, message, pc, sampleSet, loopVariant>>

LoopLabels  == {"RequireColorAssignment", "ExecuteSlushLoop",
                "CollectResponses", "Done"}
QueryLabels == {"QueryReplyLoop", "Done"}

TypeInvariant ==
    /\ pick \in [Node -> Color \cup {NoColor}]
    /\ message \subseteq Message
    /\ NoMessage \notin message
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> LoopLabels \cup QueryLabels]
    /\ \A p \in SlushLoopProcess : pc[p] \in LoopLabels
    /\ \A p \in SlushQueryProcess : pc[p] \in QueryLabels
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]

PendingQueryMessage(n) ==
    {m \in message : m.type = QueryMessageType /\ m.dst = n}

PendingQueryReplyMessage(n, srcs) ==
    {m \in message : m.type = QueryReplyMessageType /\ m.dst = n /\ m.src \in srcs}

Init ==
    /\ pick = [n \in Node |-> NoColor]
    /\ message = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |->
                IF p \in SlushLoopProcess THEN "RequireColorAssignment"
                                          ELSE "QueryReplyLoop"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopVariant = [p \in SlushLoopProcess |-> 0]

(***************************************************************************)
(* External client assigns a color to an uncolored node.                  *)
(***************************************************************************)
ClientRequest ==
    \E n \in Node, c \in Color :
        /\ pick[n] = NoColor
        /\ pick' = [pick EXCEPT ![n] = c]
        /\ UNCHANGED <<message, pc, sampleSet, loopVariant>>

(***************************************************************************)
(* Slush loop process actions.                                            *)
(***************************************************************************)
RequireColorAssignment(self) ==
    LET host == HostMapping[self] IN
    /\ pc[self] = "RequireColorAssignment"
    /\ pick[host] /= NoColor
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
    LET host == HostMapping[self] IN
    /\ pc[self] = "ExecuteSlushLoop"
    /\ IF loopVariant[self] < SlushIterationCount
       THEN \E sample \in SUBSET (Node \ {host}) :
              /\ Cardinality(sample) = SampleSetSize
              /\ sampleSet' = [sampleSet EXCEPT ![self] = sample]
              /\ message' = message \cup
                    {[type  |-> QueryMessageType,
                      src   |-> host,
                      dst   |-> s,
                      color |-> pick[host]] : s \in sample}
              /\ pc' = [pc EXCEPT ![self] = "CollectResponses"]
              /\ UNCHANGED <<pick, loopVariant>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

CollectResponses(self) ==
    LET host    == HostMapping[self]
        replies == PendingQueryReplyMessage(host, sampleSet[self])
    IN
    /\ pc[self] = "CollectResponses"
    /\ \A s \in sampleSet[self] : \E m \in replies : m.src = s
    /\ message' = message \ replies
    /\ \/ \E c \in Color :
            /\ Cardinality({m \in replies : m.color = c}) >= PickFlipThreshold
            /\ pick' = [pick EXCEPT ![host] = c]
       \/ /\ \A c \in Color :
                Cardinality({m \in replies : m.color = c}) < PickFlipThreshold
          /\ UNCHANGED pick
    /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
    /\ loopVariant' = [loopVariant EXCEPT ![self] = @ + 1]
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoop(self) ==
    \/ RequireColorAssignment(self)
    \/ ExecuteSlushLoop(self)
    \/ CollectResponses(self)

(***************************************************************************)
(* Slush query process actions.                                           *)
(***************************************************************************)
ReplyToQuery(self) ==
    LET host == HostMapping[self] IN
    /\ pc[self] = "QueryReplyLoop"
    /\ \E m \in PendingQueryMessage(host) :
         LET newColor == IF pick[host] = NoColor THEN m.color ELSE pick[host] IN
         /\ pick' = [pick EXCEPT ![host] = newColor]
         /\ message' = (message \ {m}) \cup
               {[type  |-> QueryReplyMessageType,
                 src   |-> host,
                 dst   |-> m.src,
                 color |-> newColor]}
    /\ UNCHANGED <<pc, sampleSet, loopVariant>>

QueryTerminate(self) ==
    LET host == HostMapping[self] IN
    /\ pc[self] = "QueryReplyLoop"
    /\ PendingQueryMessage(host) = {}
    /\ \A p \in SlushLoopProcess : pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

SlushQuery(self) ==
    \/ ReplyToQuery(self)
    \/ QueryTerminate(self)

Terminating ==
    /\ \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ClientRequest
    \/ \E self \in SlushLoopProcess : SlushLoop(self)
    \/ \E self \in SlushQueryProcess : SlushQuery(self)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ClientRequest)
    /\ \A self \in SlushLoopProcess : WF_vars(SlushLoop(self))
    /\ \A self \in SlushQueryProcess : WF_vars(SlushQuery(self))

Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "Done")

Terminates == <>(\A p \in SlushLoopProcess : pc[p] = "Done")

=============================================================================