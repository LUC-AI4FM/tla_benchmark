-------------------------------- MODULE Slush --------------------------------
(***************************************************************************)
(* A specification of the Slush protocol, a simple consensus algorithm     *)
(* from the Avalanche family. Nodes hold colors. Loop processes repeatedly *)
(* query sampled peers and may flip their node's color. Query processes    *)
(* answer queries with their node's current color. A client process        *)
(* assigns colors to uncolored nodes.                                      *)
(*                                                                         *)
(* The protocol is meant to be probabilistic, but this model is not. It is *)
(* mainly useful as executable pseudocode plus basic temporal checking.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                \* The set of nodes
    SlushLoopProcess,    \* The set of Slush loop process identifiers
    SlushQueryProcess,   \* The set of Slush query process identifiers
    HostMapping,         \* Set of tuples <<node, loopProcess, queryProcess>>
    SlushIterationCount, \* Number of iterations each Slush loop executes
    SampleSetSize,       \* Number of peers sampled in each iteration
    PickFlipThreshold,   \* Number of same-color replies needed to flip
    NoColor,             \* Placeholder value for an uncolored node
    NoMessage            \* Placeholder value for the absence of a message

ASSUME SlushIterationCount \in Nat
ASSUME SampleSetSize \in Nat
ASSUME PickFlipThreshold \in Nat

Red == "Red"
Blue == "Blue"
Color == {Red, Blue}

ASSUME NoColor \notin Color

QueryMessageType == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"
MessageType == {QueryMessageType, QueryReplyMessageType}

Message ==
    [src : Node, dst : Node, type : MessageType, color : Color \cup {NoColor}]

SlushClientProcess == "SlushClientProcess"

HostOf(pid) ==
    CHOOSE n \in Node :
        \E m \in HostMapping : m[1] = n /\ (m[2] = pid \/ m[3] = pid)

(***************************************************************************
--algorithm Slush
variables
    color = [n \in Node |-> NoColor],
    message = {};

fair process SlushQuery \in SlushQueryProcess
begin
QueryReplyLoop:
    either
        with m \in {m \in message : m.type = QueryMessageType
                                    /\ m.dst = HostOf(self)} do
            if color[m.dst] = NoColor then color[m.dst] := m.color end if;
            message := (message \ {m}) \cup
                {[src |-> m.dst, dst |-> m.src,
                  type |-> QueryReplyMessageType, color |-> color'[m.dst]]};
        end with;
        goto QueryReplyLoop;
    or
        await \A p \in SlushLoopProcess : pc[p] = "Done";
    end either;
end process;

fair process SlushLoop \in SlushLoopProcess
variables sampleSet = {}, loopVariant = 0;
begin
RequireColor:
    await color[HostOf(self)] /= NoColor;
ExecuteSlushLoop:
    while loopVariant < SlushIterationCount do
      QuerySampleSet:
        with s \in {ss \in SUBSET (Node \ {HostOf(self)}) :
                        Cardinality(ss) = SampleSetSize} do
            sampleSet := s;
            message := message \cup
                {[src |-> HostOf(self), dst |-> n, type |-> QueryMessageType,
                  color |-> color[HostOf(self)]] : n \in s};
        end with;
      TallyQueryReplies:
        await all replies received;
        flip color if a threshold of replies has the same color;
        consume replies; sampleSet := {}; loopVariant := loopVariant + 1;
    end while;
end process;

fair process SlushClient = SlushClientProcess
begin
ClientRequest:
    if \E n \in Node : color[n] = NoColor then
        with n \in {n \in Node : color[n] = NoColor}, c \in Color do
            color[n] := c;
        end with;
        goto ClientRequest;
    end if;
end process;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES color, message, pc, sampleSet, loopVariant

vars == << color, message, pc, sampleSet, loopVariant >>

ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup {SlushClientProcess}

ASSUME NoMessage \notin Message

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ message = {}
    /\ sampleSet = [self \in SlushLoopProcess |-> {}]
    /\ loopVariant = [self \in SlushLoopProcess |-> 0]
    /\ pc = [self \in ProcSet |->
                CASE self \in SlushQueryProcess -> "QueryReplyLoop"
                  [] self \in SlushLoopProcess -> "RequireColor"
                  [] self = SlushClientProcess -> "ClientRequest"]

QueryReplyLoop(self) ==
    /\ pc[self] = "QueryReplyLoop"
    /\ \/ /\ \E m \in message :
                /\ m.type = QueryMessageType
                /\ m.dst = HostOf(self)
                /\ LET newColor == IF color[m.dst] = NoColor
                                     THEN m.color
                                     ELSE color[m.dst]
                   IN /\ color' = [color EXCEPT ![m.dst] = newColor]
                      /\ message' = (message \ {m}) \cup
                            {[src |-> m.dst, dst |-> m.src,
                              type |-> QueryReplyMessageType,
                              color |-> newColor]}
          /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
       \/ /\ \A p \in SlushLoopProcess : pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![self] = "Done"]
          /\ UNCHANGED << color, message >>
    /\ UNCHANGED << sampleSet, loopVariant >>

SlushQuery(self) == QueryReplyLoop(self)

RequireColor(self) ==
    /\ pc[self] = "RequireColor"
    /\ color[HostOf(self)] /= NoColor
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
    /\ UNCHANGED << color, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) ==
    /\ pc[self] = "ExecuteSlushLoop"
    /\ IF loopVariant[self] < SlushIterationCount
         THEN pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
         ELSE pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << color, message, sampleSet, loopVariant >>

QuerySampleSet(self) ==
    /\ pc[self] = "QuerySampleSet"
    /\ \E s \in {ss \in SUBSET (Node \ {HostOf(self)}) :
                    Cardinality(ss) = SampleSetSize} :
          /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
          /\ message' = message \cup
                {[src |-> HostOf(self), dst |-> n, type |-> QueryMessageType,
                  color |-> color[HostOf(self)]] : n \in s}
    /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
    /\ UNCHANGED << color, loopVariant >>

TallyQueryReplies(self) ==
    LET host == HostOf(self)
        replies == {m \in message : /\ m.type = QueryReplyMessageType
                                    /\ m.dst = host
                                    /\ m.src \in sampleSet[self]}
        redTally == Cardinality({m \in replies : m.color = Red})
        blueTally == Cardinality({m \in replies : m.color = Blue})
    IN
    /\ pc[self] = "TallyQueryReplies"
    /\ \A n \in sampleSet[self] : \E m \in replies : m.src = n
    /\ color' = [color EXCEPT ![host] =
                    IF redTally >= PickFlipThreshold THEN Red
                    ELSE IF blueTally >= PickFlipThreshold THEN Blue
                    ELSE @]
    /\ message' = message \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
    /\ loopVariant' = [loopVariant EXCEPT ![self] = @ + 1]
    /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoop(self) ==
    \/ RequireColor(self)
    \/ ExecuteSlushLoop(self)
    \/ QuerySampleSet(self)
    \/ TallyQueryReplies(self)

ClientRequest ==
    /\ pc[SlushClientProcess] = "ClientRequest"
    /\ IF \E n \in Node : color[n] = NoColor
         THEN /\ \E n \in {x \in Node : color[x] = NoColor} :
                   \E c \in Color :
                      color' = [color EXCEPT ![n] = c]
              /\ pc' = [pc EXCEPT ![SlushClientProcess] = "ClientRequest"]
         ELSE /\ pc' = [pc EXCEPT ![SlushClientProcess] = "Done"]
              /\ UNCHANGED color
    /\ UNCHANGED << message, sampleSet, loopVariant >>

SlushClient == ClientRequest

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ SlushClient
    \/ (\E self \in SlushQueryProcess : SlushQuery(self))
    \/ (\E self \in SlushLoopProcess : SlushLoop(self))
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in SlushQueryProcess : WF_vars(SlushQuery(self))
    /\ \A self \in SlushLoopProcess : WF_vars(SlushLoop(self))
    /\ WF_vars(SlushClient)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")
\* END TRANSLATION

TypeInvariant ==
    /\ color \in [Node -> Color \cup {NoColor}]
    /\ message \subseteq Message
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]
    /\ pc \in [ProcSet -> {"QueryReplyLoop", "RequireColor",
                           "ExecuteSlushLoop", "QuerySampleSet",
                           "TallyQueryReplies", "ClientRequest", "Done"}]

=============================================================================