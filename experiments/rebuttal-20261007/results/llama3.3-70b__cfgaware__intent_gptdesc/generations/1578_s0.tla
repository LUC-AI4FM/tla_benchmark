---------------------------- MODULE DequeSpec ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Null, Full, Empty, ValSet
VARIABLE head, tail, nodes, pool, gcNodes, clients

defaultInitValue == <<Null, Null, {}, {}, {}, {}>>

TypeInvariant ==
  /\ head \in [nodes -> Node |-> Null]
  /\ tail \in [nodes -> Node |-> Null]
  /\ nodes \in [Node -> {left: Node, right: Node, val: ValSet}]
  /\ pool \in [Pool -> BOOLEAN]
  /\ gcNodes \in [Node -> BOOLEAN]
  /\ clients \in [Client -> {op: {"pushLeft", "pushRight", "popLeft", "popRight"}, 
                             arg: ValSet, ret: {Full, Empty, ValSet}}]

Spec ==
  /\ TypeInvariant
  /\ Init
  /\ [][Next]_clients

Init ==
  /\ head = [n \in Node |-> Null]
  /\ tail = [n \in Node |-> Null]
  /\ nodes = {}
  /\ pool = [p \in Pool |-> TRUE]
  /\ gcNodes = {}
  /\ clients = {}

PushLeftPre(client) == 
  /\ clients[client].op = "pushLeft"
  /\ clients[client].arg \in ValSet
  /\ \E p \in Pool : pool[p] = TRUE

PushLeft(client) ==
  /\ \E n \in Node, p \in Pool :
      /\ nodes' = [nodes EXCEPT ![n] = <<left: Null, right: head[n], val: clients[client].arg>>]
      /\ pool' = [pool EXCEPT ![p] = FALSE]
      /\ head' = [head EXCEPT ![n] = n]
  /\ gcNodes' = gcNodes
  /\ clients' = [clients EXCEPT ![client] = <<op: "pushLeft", arg: clients[client].arg, ret: Null>>]

PushRightPre(client) == 
  /\ clients[client].op = "pushRight"
  /\ clients[client].arg \in ValSet
  /\ \E p \in Pool : pool[p] = TRUE

PushRight(client) ==
  /\ \E n \in Node, p \in Pool :
      /\ nodes' = [nodes EXCEPT ![n] = <<left: tail[n], right: Null, val: clients[client].arg>>]
      /\ pool' = [pool EXCEPT ![p] = FALSE]
      /\ tail' = [tail EXCEPT ![n] = n]
  /\ gcNodes' = gcNodes
  /\ clients' = [clients EXCEPT ![client] = <<op: "pushRight", arg: clients[client].arg, ret: Null>>]

PopLeftPre(client) == 
  /\ clients[client].op = "popLeft"
  /\ head \in [n \in Node |-> n]
  /\ nodes[head[n]].left = Null

PopLeft(client) ==
  /\ \E v \in ValSet :
      /\ clients' = [clients EXCEPT ![client] = <<op: "popLeft", arg: Null, ret: v>>]
      /\ head' = [head EXCEPT ![n] = nodes[head[n]].right]
      /\ gcNodes' = gcNodes \cup {head[n]}
  /\ nodes' = [nodes EXCEPT \{head[n]\}]
  /\ pool' = pool
  /\ tail' = tail

PopRightPre(client) == 
  /\ clients[client].op = "popRight"
  /\ tail \in [n \in Node |-> n]
  /\ nodes[tail[n]].right = Null

PopRight(client) ==
  /\ \E v \in ValSet :
      /\ clients' = [clients EXCEPT ![client] = <<op: "popRight", arg: Null, ret: v>>]
      /\ tail' = [tail EXCEPT ![n] = nodes[tail[n]].left]
      /\ gcNodes' = gcNodes \cup {tail[n]}
  /\ nodes' = [nodes EXCEPT \{tail[n]\}]
  /\ pool' = pool
  /\ head' = head

GCPre == 
  /\ \E n \in Node : gcNodes[n] = TRUE

GCTrans ==
  /\ gcNodes' = [gcNodes EXCEPT ![n] = FALSE]
  /\ nodes' = [nodes EXCEPT \{n\}]
  /\ pool' = [pool EXCEPT ![p] = TRUE]

Next == 
  \/ \E c \in Client : PushLeftPre(c) /\ PushLeft(c)
  \/ \E c \in Client : PushRightPre(c) /\ PushRight(c)
  \/ \E c \in Client : PopLeftPre(c) /\ PopLeft(c)
  \/ \E c \in Client : PopRightPre(c) /\ PopRight(c)
  \/ GCPre /\ GCTrans
  \/ \E c \in Client : clients[c].op = "pushLeft" /\ clients' = [clients EXCEPT ![c] = <<op: "pushLeft", arg: clients[c].arg, ret: Full>>]
  \/ \E c \in Client : clients[c].op = "pushRight" /\ clients' = [clients EXCEPT ![c] = <<op: "pushRight", arg: clients[c].arg, ret: Full>>]
  \/ \E c \in Client : clients[c].op = "popLeft" /\ clients' = [clients EXCEPT ![c] = <<op: "popLeft", arg: Null, ret: Empty>>]
  \/ \E c \in Client : clients[c].op = "popRight" /\ clients' = [clients EXCEPT ![c] = <<op: "popRight", arg: Null, ret: Empty>>]

=============================================================================