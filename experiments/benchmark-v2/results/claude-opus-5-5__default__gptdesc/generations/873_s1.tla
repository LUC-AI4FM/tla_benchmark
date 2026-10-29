------------------------------- MODULE Slush -------------------------------
(***************************************************************************)
(* Specification of the Slush protocol, a simple consensus algorithm from  *)
(* the Avalanche family. Nodes hold colors. Each node runs a loop process  *)
(* that repeatedly samples peers and queries their colors, and a query     *)
(* process that answers queries with the node's current color. A client    *)
(* process assigns initial colors to uncolored nodes.                      *)
(*                                                                         *)
(* NOTE: Slush is a probabilistic protocol, but this TLA+ model is not     *)
(* probabilistic. It is mainly useful as executable pseudocode plus basic  *)
(* temporal checking, such as termination of all processes.               *)
(*                                                                         *)
(* The definitions below follow the shape of a PlusCal translation: there  *)
(* is a pc variable over labels, one action per label, and an explicit     *)
(* Terminating action that stutters once every process reaches "Done".     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,                \* The set of nodes
  SlushLoopProcess,    \* Loop process identifiers, one per node
  SlushQueryProcess,   \* Query process identifiers, one per node
  ClientProcess,       \* Identifier of the client process
  HostMapping,         \* Set of records [node, loop, query]
  SlushIterationCount, \* Number of Slush loop iterations per node
  SampleSetSize        \* Number of peers sampled in each iteration

Red   == "Red"
Blue  == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c : c \notin Color

QueryMessageType    == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"

ASSUME HostMappingType ==
  /\ HostMapping \subseteq [node : Node, loop : SlushLoopProcess, query : SlushQueryProcess]
  /\ \A n \in Node : \E r \in HostMapping : r.node = n
  /\ \A p \in SlushLoopProcess : \E r \in HostMapping : r.loop = p
  /\ \A p \in SlushQueryProcess : \E r \in HostMapping : r.query = p
  /\ \A r1, r2 \in HostMapping :
       (r1.node = r2.node \/ r1.loop = r2.loop \/ r1.query = r2.query) => r1 = r2

ASSUME ProcessesDisjoint ==
  /\ SlushLoopProcess \cap SlushQueryProcess = {}
  /\ ClientProcess \notin SlushLoopProcess
  /\ ClientProcess \notin SlushQueryProcess

ASSUME ParameterAssumption ==
  /\ SlushIterationCount \in Nat
  /\ SampleSetSize \in Nat \ {0}
  /\ SampleSetSize <= Cardinality(Node) - 1

HostOf(p) == (CHOOSE r \in HostMapping : r.loop = p \/ r.query = p).node

Message ==
  [type : {QueryMessageType}, src : SlushLoopProcess, dst : Node, color : Color]
  \cup
  [type : {QueryReplyMessageType}, src : Node, dst : SlushLoopProcess, color : Color]

PossibleSamples(self) ==
  {s \in SUBSET (Node \ {HostOf(self)}) : Cardinality(s) = SampleSetSize}

VARIABLES color, message, pc, sampleSet, loopVariant

vars == <<color, message, pc, sampleSet, loopVariant>>

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {ClientProcess}

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]
  /\ pc = [self \in ProcSet |->
             CASE self \in SlushLoopProcess  -> "RequireColorAssignment"
               [] self \in SlushQueryProcess -> "QueryReplyLoop"
               [] self = ClientProcess       -> "ClientRequest"]

(***************************************************************************)
(* Slush loop process                                                      *)
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
  /\ pc[self] = "QuerySampleSet"
  /\ \E s \in PossibleSamples(self) :
       /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
       /\ message' = message \cup
            {[type  |-> QueryMessageType,
              src   |-> self,
              dst   |-> n,
              color |-> color[HostOf(self)]] : n \in s}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED <<color, loopVariant>>

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ LET replies == {m \in message : m.type = QueryReplyMessageType /\ m.dst = self}
         Tally(c) == Cardinality({m \in replies : m.color = c})
         Majority == {c \in Color : Tally(c) > SampleSetSize \div 2}
     IN /\ {m.src : m \in replies} = sampleSet[self]
        /\ message' = message \ replies
        /\ color' = IF Majority # {}
                      THEN [color EXCEPT ![HostOf(self)] = CHOOSE c \in Majority : TRUE]
                      ELSE color
  /\ loopVariant' = [loopVariant EXCEPT ![self] = @ + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED sampleSet

SlushLoop(self) ==
  \/ RequireColorAssignment(self)
  \/ ExecuteSlushLoop(self)
  \/ QuerySampleSet(self)
  \/ TallyQueryReplies(self)

(***************************************************************************)
(* Slush query process                                                     *)
(***************************************************************************)
PendingQueries(self) ==
  {m \in message : m.type = QueryMessageType /\ m.dst = HostOf(self)}

QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ \/ /\ PendingQueries(self) # {}
        /\ \E m \in PendingQueries(self) :
             LET host == HostOf(self)
                 newColor == IF color[host] = NoColor THEN m.color ELSE color[host]
             IN /\ color' = [color EXCEPT ![host] = newColor]
                /\ message' = (message \ {m}) \cup
                     {[type  |-> QueryReplyMessageType,
                       src   |-> host,
                       dst   |-> m.src,
                       color |-> newColor]}
        /\ UNCHANGED pc
     \/ /\ PendingQueries(self) = {}
        /\ \A p \in SlushLoopProcess : pc[p] = "Done"
        /\ pc' = [pc EXCEPT ![self] = "Done"]
        /\ UNCHANGED <<color, message>>
  /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(self) == QueryReplyLoop(self)

(***************************************************************************)
(* Client process                                                          *)
(***************************************************************************)
ClientRequest(self) ==
  /\ pc[self] = "ClientRequest"
  /\ LET Uncolored == {n \in Node : color[n] = NoColor} IN
       IF Uncolored # {}
         THEN /\ \E n \in Uncolored, c \in Color :
                   color' = [color EXCEPT ![n] = c]
              /\ UNCHANGED pc
         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED color
  /\ UNCHANGED <<message, sampleSet, loopVariant>>

Client == ClientRequest(ClientProcess)

(***************************************************************************)
(* Explicit terminating stuttering step, preventing deadlock when all      *)
(* processes are done.                                                     *)
(***************************************************************************)
Terminating ==
  /\ \A self \in ProcSet : pc[self] = "Done"
  /\ UNCHANGED vars

Next ==
  \/ Client
  \/ (\E self \in SlushLoopProcess : SlushLoop(self))
  \/ (\E self \in SlushQueryProcess : SlushQuery(self))
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A self \in SlushLoopProcess : WF_vars(SlushLoop(self))
  /\ \A self \in SlushQueryProcess : WF_vars(SlushQuery(self))
  /\ WF_vars(Client)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeInvariant ==
  /\ color \in [Node -> Color \cup {NoColor}]
  /\ message \subseteq Message
  /\ pc \in [ProcSet -> {"RequireColorAssignment", "ExecuteSlushLoop",
                         "QuerySampleSet", "TallyQueryReplies",
                         "QueryReplyLoop", "ClientRequest", "Done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

=============================================================================