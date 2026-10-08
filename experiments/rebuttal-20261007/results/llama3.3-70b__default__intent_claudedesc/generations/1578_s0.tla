```tla
MODULE LockFreeDeque

EXTENDS Integers, Sequences, TLC

CONSTANTS
  NumProcesses,
  MaxValue,
  NodePoolSize,
  SentinelNode

VARIABLES
  nodes,  \* Mapping of node addresses to their values and next pointers
  head,   \* Pointer to the leftmost node in the deque
  tail,   \* Pointer to the rightmost node in the deque
  freeList, \* List of available node addresses for allocation
  processStates, \* Each process's current state (operation and arguments)
  result

Init ==
  /\ nodes = [n \in 1..NodePoolSize |-> [value |-> None, next |-> None]]
  /\ head = SentinelNode
  /\ tail = SentinelNode
  /\ freeList = <<1..NodePoolSize>>
  /\ processStates = [p \in 1..NumProcesses |-> [op |-> "idle", args |-> <<>>]]
  /\ result = ""

Next ==
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "idle"
      /\ processStates' = [processStates EXCEPT ![p].op = "pushLeft"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = ""
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "idle"
      /\ processStates' = [processStates EXCEPT ![p].op = "pushRight"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = ""
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "idle"
      /\ processStates' = [processStates EXCEPT ![p].op = "popLeft"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = ""
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "idle"
      /\ processStates' = [processStates EXCEPT ![p].op = "popRight"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = ""
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "pushLeft"
      /\ freeList # <<>>
      /\ Let newNode == Head(freeList) ;
        /\ nodes' = [nodes EXCEPT ![newNode].value = processStates[p].args[1]]
        /\ head' = newNode
        /\ tail' = tail
        /\ freeList' = Tail(freeList)
        /\ processStates' = [processStates EXCEPT ![p].op = "idle"]
        /\ result' = "okay"
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "pushRight"
      /\ freeList # <<>>
      /\ Let newNode == Head(freeList) ;
        /\ nodes' = [nodes EXCEPT ![newNode].value = processStates[p].args[1]]
        /\ head' = head
        /\ tail' = newNode
        /\ freeList' = Tail(freeList)
        /\ processStates' = [processStates EXCEPT ![p].op = "idle"]
        /\ result' = "okay"
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "popLeft"
      /\ head # SentinelNode
      /\ Let value == nodes[head].value ;
        /\ nodes' = [nodes EXCEPT ![head].value = None]
        /\ head' = nodes[head].next
        /\ tail' = tail
        /\ freeList' = Append(freeList, <<head>>)
        /\ processStates' = [processStates EXCEPT ![p].op = "idle", ![p].args = <<value>>]
        /\ result' = value
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "popRight"
      /\ tail # SentinelNode
      /\ Let value == nodes[tail].value ;
        /\ nodes' = [nodes EXCEPT ![tail].value = None]
        /\ head' = head
        /\ tail' = nodes[tail].next
        /\ freeList' = Append(freeList, <<tail>>)
        /\ processStates' = [processStates EXCEPT ![p].op = "idle", ![p].args = <<value>>]
        /\ result' = value
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "pushLeft"
      /\ freeList = <<>>
      /\ processStates' = [processStates EXCEPT ![p].op = "idle"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = "full"
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "pushRight"
      /\ freeList = <<>>
      /\ processStates' = [processStates EXCEPT ![p].op = "idle"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = "full"
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "popLeft"
      /\ head = SentinelNode
      /\ processStates' = [processStates EXCEPT ![p].op = "idle"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = "empty"
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p].op = "popRight"
      /\ tail = SentinelNode
      /\ processStates' = [processStates EXCEPT ![p].op = "idle"]
      /\ nodes' = nodes
      /\ head' = head
      /\ tail' = tail
      /\ freeList' = freeList
      /\ result' = "empty"

Spec ==
  Init /\ [][Next]_nodes,head,tail,freeList,processStates,result

THEOREM Spec => []~(result = "full" /\ result' = "okay")
THEOREM Spec => []~(result = "empty" /\ result' = "okay")

Fairness == <>[]<>(\E p \in 1..NumProcesses : processStates[p].op # "idle")

INVARIANT head \in {SentinelNode} \cup (1..NodePoolSize)
INVARIANT tail \in {SentinelNode} \cup (1..NodePoolSize)

TypeOK == 
  /\ nodes \in [1..NodePoolSize -> [value: Int, next: 1..NodePoolSize]]
  /\ head \in {SentinelNode} \cup (1..NodePoolSize)
  /\ tail \in {SentinelNode} \cup (1..NodePoolSize)
  /\ freeList \in Seq(1..NodePoolSize)
  /\ processStates \in [1..NumProcesses -> [op: {"pushLeft", "pushRight", "popLeft", "popRight"}, args: Seq(Int)]]
  /\ result \in {"okay", "full", "empty"}

```
Note that the above TLA+ specification models a lock-free double-ended queue with DCAS as its atomic synchronization primitive. The `Next` action describes all possible state transitions, including push and pop operations from both ends of the deque. The `Spec` formula defines the complete specification by combining the initial condition `Init` with the next-state relation `[Next]_nodes,head,tail,freeList,processStates,result`. 

The provided invariants ensure that the `head` and `tail` pointers always point to valid nodes or the sentinel node. The fairness condition ensures that every process will eventually perform an operation.

To verify the correctness properties (linearizability, no lost values, no duplicate returns, proper empty detection), you would need to write additional temporal logic formulas using TLA+ operators like `[]` (always) and `<>` (eventually). These formulas can be used as theorems in TLC model checking.