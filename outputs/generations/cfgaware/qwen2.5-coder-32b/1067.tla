------------------------------- MODULE TerminationDetection ------------------------------

CONSTANTS Node

VARIABLES activeNodes, terminationDetected

(* --algorithm TerminationDetection
variables activeNodes = Node, terminationDetected = FALSE;

fair process (node \in Node)
vars nextNode = (node + 1) % Cardinality(Node)
begin
    while TRUE do
        if node \notin activeNodes then
            await node \in activeNodes;
        else
            either
                /\ with probability 0.5 do
                    terminationDetected := FALSE;
                    activeNodes := activeNodes \ {node};
                [] /\ with probability 0.5 do
                    if nextNode \in activeNodes then
                        skip;
                    else
                        activeNodes := activeNodes \union {nextNode};
            end either;
        end if;
    od;
end process;

fair action Detection =
    if activeNodes = {} then
        terminationDetected := TRUE;
    end if;

correctness == <>[] (terminationDetected => (activeNodes = {}))

quiescence == []<>(activeNodes = {})

liveness == <>(terminationDetected)

end algorithm *)

Spec ==
  /\ Init
  /\ [][Next]_<<node \in Node>>
  /\ WF_[Next]_<<node \in Node>>
  /\ SF_Detection

Init ==
  /\ activeNodes = Node
  /\ terminationDetected = FALSE

Next ==
  \/ \E node \in Node : NodeAction(node)
  \/ Detection

NodeAction(node) ==
  \/ /\ node \notin activeNodes
     /\ UNCHANGED <<activeNodes, terminationDetected>>
  \/ /\ node \in activeNodes
     /\ (terminationDetected' = FALSE) 
        /\ (activeNodes' = activeNodes \ {node})
  \/ /\ node \in activeNodes
     /\ LET nextNode = (node + 1) % Cardinality(Node)
        IN /\ nextNode \notin activeNodes
           /\ (activeNodes' = activeNodes \union {nextNode})
           /\ UNCHANGED terminationDetected

Detection ==
  /\ IF activeNodes = {} THEN terminationDetected' = TRUE ELSE terminationDetected' = terminationDetected
  /\ UNCHANGED activeNodes

SF_Detection == <<>> \in StableFair(Detection)

StableFair(A) == \/ A
                 \/ <>([]~A /\ <>A)

WF_(A)_vars ==
  /\ A => (UNION {PCs'[p] : p \in vars} = {})
  /\ ~A => (\E p \in vars : PCs'[p] \notin {})

WF_[Next]_<<node \in Node>> == WF_(Next)_<<node>>

================================================================================