---------------------------- MODULE ParityCheck ----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

ASSUME NInNat == N \in Nat

VARIABLES result, n, stack, pc, calls

vars == << result, n, stack, pc, calls >>

Labels == {"Start", "IE1", "IERet", "IO1", "IORet", "Done"}

Init == /\ result = FALSE
        /\ n = 0
        /\ stack = << >>
        /\ pc = "Start"
        /\ calls = 0

(* main program: invoke IsEven(N), return to "Done" *)
Start == /\ pc = "Start"
         /\ stack' = << [ procedure |-> "IsEven", pc |-> "Done", n |-> n ] >> \o stack
         /\ n' = N
         /\ pc' = "IE1"
         /\ calls' = calls + 1
         /\ UNCHANGED result

(* procedure IsEven(n) *)
IE1 == /\ pc = "IE1"
       /\ IF n = 0
            THEN /\ result' = TRUE
                 /\ pc' = "IERet"
                 /\ UNCHANGED << n, stack, calls >>
            ELSE /\ stack' = << [ procedure |-> "IsOdd", pc |-> "IERet", n |-> n ] >> \o stack
                 /\ n' = n - 1
                 /\ pc' = "IO1"
                 /\ calls' = calls + 1
                 /\ UNCHANGED result

IERet == /\ pc = "IERet"
         /\ pc' = Head(stack).pc
         /\ n' = Head(stack).n
         /\ stack' = Tail(stack)
         /\ UNCHANGED << result, calls >>

(* procedure IsOdd(n) *)
IO1 == /\ pc = "IO1"
       /\ IF n = 0
            THEN /\ result' = FALSE
                 /\ pc' = "IORet"
                 /\ UNCHANGED << n, stack, calls >>
            ELSE /\ stack' = << [ procedure |-> "IsEven", pc |-> "IORet", n |-> n ] >> \o stack
                 /\ n' = n - 1
                 /\ pc' = "IE1"
                 /\ calls' = calls + 1
                 /\ UNCHANGED result

IORet == /\ pc = "IORet"
         /\ pc' = Head(stack).pc
         /\ n' = Head(stack).n
         /\ stack' = Tail(stack)
         /\ UNCHANGED << result, calls >>

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Start \/ IE1 \/ IERet \/ IO1 \/ IORet \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK == /\ result \in BOOLEAN
          /\ n \in Nat
          /\ pc \in Labels
          /\ calls \in Nat

(* The number of calls ever made is bounded by N + 1 *)
PossibleCounts == calls \in 0..(N + 1)

StackBounded == Len(stack) <= N + 1

(* Stack safety: return locations and saved local arguments are never corrupted *)
StackSafe ==
    (pc \notin {"Start", "Done"}) =>
        /\ Len(stack) >= 1
        /\ stack[Len(stack)].pc = "Done"
        /\ stack[Len(stack)].procedure = "IsEven"
        /\ n + Len(stack) - 1 = N
        /\ \A i \in 1..(Len(stack) - 1) :
               /\ stack[i].n = n + i
               /\ stack[i].pc \in {"IERet", "IORet"}

(* After termination no procedure is active and the stack is empty *)
DoneClean == (pc = "Done") => (stack = << >> /\ n = 0)

StartClean == (pc = "Start") => (stack = << >> /\ calls = 0)

Correctness == (pc = "Done") => (result = (N % 2 = 0))

Inv == /\ TypeOK
       /\ PossibleCounts
       /\ StackBounded
       /\ StackSafe
       /\ DoneClean
       /\ StartClean
       /\ Correctness

-----------------------------------------------------------------------------
(* Liveness / temporal properties *)

Termination == <>(pc = "Done")

EventuallyCorrect == <>[](pc = "Done" /\ result = (N % 2 = 0) /\ stack = << >>)

ResultStable == [][(pc = "Done") => UNCHANGED << result, stack, pc >>]_vars

=============================================================================