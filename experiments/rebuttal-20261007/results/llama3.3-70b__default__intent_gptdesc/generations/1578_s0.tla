```tla
MODULE DequeSpec

EXTENDS Integers, Sequences, TLC

CONSTANTS
  NodePoolSize,
  NullNode,
  SentinelNode,
  ErrorCodeFull,
  ErrorCodeEmpty

VARIABLES
  nodes,
  head,
  tail,
  leftPushing,
  rightPushing,
  leftPopping,
  rightPopping,
  gcNodes

Init ==
  /\ nodes = [i \in 1..NodePoolSize |-> NullNode]
  /\ head = SentinelNode
  /\ tail = SentinelNode
  /\ leftPushing = {}
  /\ rightPushing = {}
  /\ leftPopping = {}
  /\ rightPopping = {}
  /\ gcNodes = {}

Next ==
  \/ \E client \in Clients :
      \/ PushLeft(client)
      \/ PushRight(client)
      \/ PopLeft(client)
      \/ PopRight(client)
  \/ GC

PushLeft(client) ==
  /\ client \notin leftPushing
  /\ \E newNode \in Nodes :
      /\ newNode \notin DOMAIN nodes
      /\ nodes' = [nodes EXCEPT ![newNode] = NullNode]
      /\ head' = IF head = SentinelNode THEN newNode ELSE head
      /\ tail' = IF tail = SentinelNode THEN newNode ELSE tail
      /\ leftPushing' = leftPushing \cup {client}
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes
  \/ \* allocation failure *
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ leftPushing' = leftPushing \cup {client}
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes

PushRight(client) ==
  /\ client \notin rightPushing
  /\ \E newNode \in Nodes :
      /\ newNode \notin DOMAIN nodes
      /\ nodes' = [nodes EXCEPT ![newNode] = NullNode]
      /\ head' = IF head = SentinelNode THEN newNode ELSE head
      /\ tail' = IF tail = SentinelNode THEN newNode ELSE tail
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing \cup {client}
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes
  \/ \* allocation failure *
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing \cup {client}
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes

PopLeft(client) ==
  /\ client \notin leftPopping
  /\ head # SentinelNode
  /\ \E value \in Values :
      /\ nodes' = [nodes EXCEPT ![head] = NullNode]
      /\ head' = IF tail = head THEN SentinelNode ELSE nodes[head]
      /\ tail' = IF tail = head THEN SentinelNode ELSE tail
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping \cup {client}
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes \cup {head}
  \/ \* empty deque *
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping \cup {client}
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes

PopRight(client) ==
  /\ client \notin rightPopping
  /\ tail # SentinelNode
  /\ \E value \in Values :
      /\ nodes' = [nodes EXCEPT ![tail] = NullNode]
      /\ head' = IF tail = head THEN SentinelNode ELSE head
      /\ tail' = IF tail = head THEN SentinelNode ELSE nodes[tail]
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping \cup {client}
      /\ gcNodes' = gcNodes \cup {tail}
  \/ \* empty deque *
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping \cup {client}
      /\ gcNodes' = gcNodes

GC ==
  /\ \E node \in gcNodes :
      /\ nodes' = [nodes EXCEPT ![node] = NullNode]
      /\ head' = IF head = node THEN SentinelNode ELSE head
      /\ tail' = IF tail = node THEN SentinelNode ELSE tail
      /\ leftPushing' = leftPushing
      /\ rightPushing' = rightPushing
      /\ leftPopping' = leftPopping
      /\ rightPopping' = rightPopping
      /\ gcNodes' = gcNodes \ {node}

Spec ==
  Init /\ [][Next]_nodes

THEOREM Spec => []TypeInvariant
THEOREM Spec => []Linearizability
THEOREM Spec => []MemorySafety
THEOREM Spec => []Progress

TypeInvariant ==
  /\ nodes \in [1..NodePoolSize -> Nodes]
  /\ head \in Nodes
  /\ tail \in Nodes
  /\ leftPushing \subseteq Clients
  /\ rightPushing \subseteq Clients
  /\ leftPopping \subseteq Clients
  /\ rightPopping \subseteq Clients
  /\ gcNodes \subseteq Nodes

Linearizability ==
  /\ \A client \in Clients :
      /\ \E op \in {PushLeft, PushRight, PopLeft, PopRight} :
          /\ op(client) => \E value \in Values : op(client, value)

MemorySafety ==
  /\ \A node \in gcNodes :
      /\ node # head
      /\ node # tail

Progress ==
  /\ \A client \in Clients :
      /\ \E op \in {PushLeft, PushRight, PopLeft, PopRight} :
          /\ op(client) => \E value \in Values : op(client, value)

Fairness ==
  /\ \A client \in Clients :
      /\ WF_vars(Next, client)
```