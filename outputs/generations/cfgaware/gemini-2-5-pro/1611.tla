---- MODULE MergeSort ----
EXTENDS Integers, Sequences, TLC

CONSTANTS ArrayLen, N, defaultInitValue

ASSUME ArrayLen \in 1..4 /\ N = ArrayLen /\ defaultInitValue = 0

VARIABLES pc, a, b, stack, len

vars == <<pc, a, b, stack, len>>

IsSorted(arr, k) == \A i \in 1..(k-1) : arr[i] <= arr[i+1]

StackFrame == [pc: STRING, l: Int, r: Int, m: Int, i: Int, j: Int, k: Int]

TypeOK ==
    /\ pc \in {"Call", "AfterLeft", "AfterRight", "MergeLoop", "CopyLeftover", "Return", "Done"}
    /\ a \in [1..ArrayLen -> 0..N]
    /\ b \in [1..ArrayLen -> 0..N]
    /\ len \in 1..ArrayLen
    /\ stack \in Seq(StackFrame)

Init ==
    /\ \E k \in 1..ArrayLen :
        /\ len = k
        /\ \E arr \in [1..k -> 1..N] :
            a = [i \in 1..ArrayLen |-> IF i <= k THEN arr[i] ELSE defaultInitValue]
    /\ b = [i \in 1..ArrayLen |-> defaultInitValue]
    /\ stack = << [pc |-> "Done", l |-> 1, r |-> len, m |-> 0, i |-> 0, j |-> 0, k |-> 0] >>
    /\ pc = "Call"

Call ==
    /\ pc = "Call"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       IF frame.l >= frame.r
       THEN /\ pc' = "Return"  \* Base case
            /\ UNCHANGED <<a, b, stack, len>>
       ELSE /\ LET m_new == (frame.l + frame.r) \div 2 IN
                 /\ LET current_frame_updated == [frame EXCEPT !.pc = "AfterLeft", !.m = m_new] IN
                 /\ LET left_call_frame == [pc |-> "Call", l |-> frame.l, r |-> m_new, m |-> 0, i |-> 0, j |-> 0, k |-> 0] IN
                 /\ stack' = <<left_call_frame>> \o <<current_frame_updated>> \o Tail(stack)
            /\ pc' = "Call"
            /\ UNCHANGED <<a, b, len>>

Return ==
    /\ pc = "Return"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       /\ pc' = frame.pc
       /\ stack' = Tail(stack)
    /\ UNCHANGED <<a, b, len>>

AfterLeft ==
    /\ pc = "AfterLeft"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       /\ LET current_frame_updated == [frame EXCEPT !.pc = "AfterRight"] IN
       /\ LET right_call_frame == [pc |-> "Call", l |-> frame.m + 1, r |-> frame.r, m |-> 0, i |-> 0, j |-> 0, k |-> 0] IN
       /\ stack' = <<right_call_frame>> \o <<current_frame_updated>> \o Tail(stack)
    /\ pc' = "Call"
    /\ UNCHANGED <<a, b, len>>

AfterRight ==
    /\ pc = "AfterRight"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       /\ b' = [b EXCEPT ![x \in frame.l..frame.r] = a[x]]
       /\ LET frame_updated == [frame EXCEPT !.i = frame.l, !.j = frame.m + 1, !.k = frame.l] IN
       /\ stack' = <<frame_updated>> \o Tail(stack)
    /\ pc' = "MergeLoop"
    /\ UNCHANGED <<a, len>>

MergeLoop ==
    /\ pc = "MergeLoop"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       /\ frame.i <= frame.m
       /\ frame.j <= frame.r
       /\ IF b[frame.i] <= b[frame.j]
          THEN /\ a' = [a EXCEPT ![frame.k] = b[frame.i]]
               /\ LET frame_updated == [frame EXCEPT !.i = frame.i + 1, !.k = frame.k + 1] IN
               /\ stack' = <<frame_updated>> \o Tail(stack)
          ELSE /\ a' = [a EXCEPT ![frame.k] = b[frame.j]]
               /\ LET frame_updated == [frame EXCEPT !.j = frame.j + 1, !.k = frame.k + 1] IN
               /\ stack' = <<frame_updated>> \o Tail(stack)
    /\ pc' = "MergeLoop"
    /\ UNCHANGED <<b, len>>

MergeLoopEnd ==
    /\ pc = "MergeLoop"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       /\ \/ frame.i > frame.m
          \/ frame.j > frame.r
    /\ pc' = "CopyLeftover"
    /\ UNCHANGED <<vars>>

CopyLeftover ==
    /\ pc = "CopyLeftover"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack) IN
       /\ IF frame.i <= frame.m
          THEN /\ a' = [a EXCEPT ![frame.k] = b[frame.i]]
               /\ LET frame_updated == [frame EXCEPT !.i = frame.i + 1, !.k = frame.k + 1] IN
               /\ stack' = <<frame_updated>> \o Tail(stack)
               /\ pc' = "CopyLeftover"
               /\ UNCHANGED <<b, len>>
          ELSE IF frame.j <= frame.r
               THEN /\ a' = [a EXCEPT ![frame.k] = b[frame.j]]
                    /\ LET frame_updated == [frame EXCEPT !.j = frame.j + 1, !.k = frame.k + 1] IN
                    /\ stack' = <<frame_updated>> \o Tail(stack)
                    /\ pc' = "CopyLeftover"
                    /\ UNCHANGED <<b, len>>
               ELSE /\ pc' = "Return"
                    /\ UNCHANGED <<vars>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Call
    \/ Return
    \/ AfterLeft
    \/ AfterRight
    \/ MergeLoop
    \/ MergeLoopEnd
    \/ CopyLeftover
    \/ Done

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

SortedAtEnd == pc = "Done" => IsSorted(a, len)

Invariant == TypeOK /\ SortedAtEnd

=============================================================================