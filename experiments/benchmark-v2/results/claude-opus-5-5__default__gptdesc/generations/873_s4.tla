------------------------------- MODULE Slush -------------------------------
(***************************************************************************)
(* Specification of the Slush protocol, the simplest member of the        *)
(* Avalanche family of consensus protocols. Nodes hold a color. A client  *)
(* assigns initial colors to uncolored nodes. Each node runs a loop        *)
(* process that repeatedly samples a set of peers, queries them for their  *)
(* color, and adopts a color if a majority of the sample reports it. Each  *)
(* node also runs a query process that answers queries with the node's     *)
(* current color. If the node has no color yet, it first adopts the       *)
(* querier's color.                                                        *)
(*                                                                         *)
(* The protocol is probabilistic in intent: its guarantees hold with high  *)
(* probability over random sampling. This TLA+ model is NOT probabilistic. *)
(* Sampling is modeled as nondeterministic choice. The spec is therefore   *)
(* mainly useful as executable pseudocode plus basic temporal checking.    *)
(* For example, it checks that all processes eventually terminate.         *)
(*                                                                         *)
(* The spec is written in the style of a translated PlusCal algorithm.     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,                 \* The set of nodes
    SlushLoopProcess,     \* Process IDs of the Slush loop processes
    SlushQueryProcess,    \* Process IDs of the Slush query processes
    ClientProcess,        \* Process ID of the client process
    HostMapping,          \* Maps each loop/query process to its host node
    SlushIterationCount,  \* Number of iterations of each Slush loop
    SampleSetSize,        \* Number of peers sampled per iteration
    Red, Blue,            \* The two colors
    NoColor               \* Marker for an uncolored node

Color == {Red, Blue}

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {ClientProcess}

ASSUME
    /\ Red # Blue
    /\ NoColor \notin Color
    /\ SlushLoopProcess \cap SlushQueryProcess = {}
    /\ ClientProcess \notin (SlushLoopProcess \cup SlushQueryProcess)
    /\ HostMapping \in [SlushLoopProcess \cup SlushQueryProcess -> Node]
    /\ \A n \in Node :
          /\ \E p \in SlushLoopProcess  : HostMapping[p] = n
          /\ \E p \in SlushQueryProcess : HostMapping[p] = n
    /\ \A p, q \in SlushLoopProcess :
          HostMapping[p] = HostMapping[q] => p = q
    /\ \A p, q \in SlushQueryProcess :
          HostMapping[p] = HostMapping[q] => p = q
    /\ SlushIterationCount \in Nat
    /\ SampleSetSize \in Nat \ {0}
    /\ SampleSetSize <= Cardinality(Node) - 1

HostOf(pid) == HostMapping[pid]

\* A color is adopted if a strict majority of the sample reports it.
Threshold == SampleSetSize \div 2

Message ==
    [type : {"QueryMessage", "QueryReply"},
     src  : Node,
     dst  : Node,
     color: Color]

(*************************** Translated PlusCal ****************************)
VARIABLES
    pick,        \* pick[n] is the current color of node n
    message,     \* Set of in-flight messages
    pc,          \* Program counter of each process
    sampleSet,   \* Local variable of loop processes: current sample
    loopVariant  \* Local variable of loop processes: iteration counter

vars == <<pick, message, pc, sampleSet, loopVariant>>

Init ==
    /\ pick = [n \in Node |-> NoColor]
    /\ message = {}
    /\ sampleSet = [self \in SlushLoopProcess |-> {}]
    /\ loopVariant = [self \in SlushLoopProcess |-> 0]
    /\ pc = [self \in ProcSet |->
                CASE self \in SlushLoopProcess  -> "RequireColorAssignment"
                  [] self \in SlushQueryProcess -> "QueryReplyLoop"
                  [] self = ClientProcess        -> "ClientRequest"]

(***************************** Query processes *****************************)

QueryReplyLoop(self) ==
    /\ pc[self] = "QueryReplyLoop"
    /\ pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

AllLoopsDone == \A p \in SlushLoopProcess : pc[p] = "Done"

PendingQueries(host) ==
    {m \in message : m.type = "QueryMessage" /\ m.dst = host}

WaitForQueryMessageOrTermination(self) ==
    LET host == HostOf(self) IN
    /\ pc[self] = "WaitForQueryMessageOrTermination"
    /\ PendingQueries(host) # {} \/ AllLoopsDone
    /\ IF AllLoopsDone
          THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED <<pick, message>>
          ELSE /\ \E m \in PendingQueries(host) :
                    LET newColor == IF pick[host] = NoColor
                                      THEN m.color
                                      ELSE pick[host]
                    IN /\ pick' = [pick EXCEPT ![host] = newColor]
                       /\ message' = (message \ {m}) \cup
                                     {[type  |-> "QueryReply",
                                       src   |-> host,
                                       dst   |-> m.src,
                                       color |-> newColor]}
               /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
    /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(self) ==
    \/ QueryReplyLoop(self)
    \/ WaitForQueryMessageOrTermination(self)

(***************************** Loop processes ******************************)

RequireColorAssignment(self) ==
    /\ pc[self] = "RequireColorAssignment"
    /\ pick[HostOf(self)] # NoColor
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
    /\ pc[self] = "ExecuteSlushLoop"
    /\ IF loopVariant[self] < SlushIterationCount
          THEN pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
          ELSE pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

QuerySampleSet(self) ==
    LET host == HostOf(self) IN
    /\ pc[self] = "QuerySampleSet"
    /\ \E s \in {x \in SUBSET (Node \ {host}) :
                    Cardinality(x) = SampleSetSize} :
          /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
          /\ message' = message \cup
                        {[type  |-> "QueryMessage",
                          src   |-> host,
                          dst   |-> n,
                          color |-> pick[host]] : n \in s}
    /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
    /\ UNCHANGED <<pick, loopVariant>>

TallyQueryReplies(self) ==
    LET host    == HostOf(self)
        replies == {m \in message : /\ m.type = "QueryReply"
                                    /\ m.dst = host
                                    /\ m.src \in sampleSet[self]}
        redTally  == Cardinality({m \in replies : m.color = Red})
        blueTally == Cardinality({m \in replies : m.color = Blue})
    IN
    /\ pc[self] = "TallyQueryReplies"
    /\ \A n \in sampleSet[self] : \E m \in replies : m.src = n
    /\ pick' = [pick EXCEPT ![host] =
                    IF redTally > Threshold THEN Red
                    ELSE IF blueTally > Threshold THEN Blue
                    ELSE pick[host]]
    /\ message' = message \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
    /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoop(self) ==
    \/ RequireColorAssignment(self)
    \/ ExecuteSlushLoop(self)
    \/ QuerySampleSet(self)
    \/ TallyQueryReplies(self)

(****************************** Client process *****************************)

UncoloredNodes == {n \in Node : pick[n] = NoColor}

ClientRequest(self) ==
    /\ pc[self] = "ClientRequest"
    /\ IF UncoloredNodes # {}
          THEN pc' = [pc EXCEPT ![self] = "AssignColorToNode"]
          ELSE pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

AssignColorToNode(self) ==
    /\ pc[self] = "AssignColorToNode"
    /\ IF UncoloredNodes # {}
          THEN \E n \in UncoloredNodes, c \in Color :
                  pick' = [pick EXCEPT ![n] = c]
          ELSE UNCHANGED pick
    /\ pc' = [pc EXCEPT ![self] = "ClientRequest"]
    /\ UNCHANGED <<message, sampleSet, loopVariant>>

Client(self) ==
    \/ ClientRequest(self)
    \/ AssignColorToNode(self)

(*************************** Next-state relation ***************************)

\* Explicit stuttering step once all processes are done, to avoid deadlock.
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Client(ClientProcess)
    \/ \E self \in SlushLoopProcess  : SlushLoop(self)
    \/ \E self \in SlushQueryProcess : SlushQuery(self)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Client(ClientProcess))
    /\ \A self \in SlushLoopProcess  : WF_vars(SlushLoop(self))
    /\ \A self \in SlushQueryProcess : WF_vars(SlushQuery(self))

(******************************* Properties ********************************)

TypeInvariant ==
    /\ pick \in [Node -> Color \cup {NoColor}]
    /\ message \subseteq Message
    /\ pc \in [ProcSet -> {"RequireColorAssignment", "ExecuteSlushLoop",
                           "QuerySampleSet", "TallyQueryReplies",
                           "QueryReplyLoop",
                           "WaitForQueryMessageOrTermination",
                           "ClientRequest", "AssignColorToNode", "Done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

THEOREM Spec => []TypeInvariant
THEOREM Spec => Termination
=============================================================================