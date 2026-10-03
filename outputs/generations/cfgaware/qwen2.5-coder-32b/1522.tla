------------------------------- MODULE HuangTermination ------------------------------

CONSTANTS Procs, Leader

VARIABLES active, weight, queue

(* --algorithm HuangTermination *)

\* Initialization
Init == /\ active = [p \in Procs |-> TRUE]
        /\ weight = [p \in Procs |-> 1.0 / Cardinality(Procs)]
        /\ queue = [p \in Procs |-> <>]

\* Message type definition
MsgType == <<Src, Dst, Wgt>> \in (Procs \X Procs \X (0.0 .. 1.0))

\* Sending action
Send(p) ==
    /\ p \in Procs
    /\ queue[p] # <>
    /\ LET msg == Head(queue[p])
       src == msg[1]
       dst == msg[2]
       wgt == msg[3]
   IN /\ weight[src]' = weight[src] - wgt
      /\ weight[dst]' = weight[dst] + wgt
      /\ queue[src]' = Tail(queue[src])
      /\ queue[dst]' = Append(queue[dst], <<src, dst, wgt>>)

\* Receiving action
Receive(p) ==
    /\ p \in Procs
    /\ queue[p] # <>
    /\ LET msg == Head(queue[p])
       src == msg[1]
       dst == msg[2]
       wgt == msg[3]
   IN /\ weight[src]' = weight[src] + wgt / 2.0
      /\ weight[dst]' = weight[dst] - wgt / 2.0
      /\ queue[src]' = Append(queue[src], <<src, dst, wgt / 2.0>>)
      /\ queue[dst]' = Tail(queue[dst])

\* Idle action
Idle(p) ==
    /\ p \in Procs
    /\ queue[p] = <>
    /\ weight[p]' = weight[p]

\* Next state relation
Next == \/ \E p \in Procs : Send(p)
        \/ \E p \in Procs : Receive(p)
        \/ \E p \in Procs : Idle(p)

\* Specification
Spec == Init /\ [][Next]_<<active, weight, queue>>

\* Termination condition
Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : queue[p] = <>

\* Safety property: Once terminated, all processes are idle and no messages are in transit.
Safety == Spec => <>[](Terminated)

\* Liveness property: Termination is eventually detected.
Liveness == Spec => [](<>[] Terminated)

=============================================================================