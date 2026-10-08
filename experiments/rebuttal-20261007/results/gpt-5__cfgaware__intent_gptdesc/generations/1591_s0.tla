------------------------------ MODULE ParityRec ------------------------------

EXTENDS Naturals, Integers, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

(*
  A simple recursive parity-checking routine modeled with an explicit call stack.
  The stack holds frames with:
    - proc ∈ {"Even","Odd"}
    - arg  ∈ Nat
    - pc   ∈ {"enter","waiting","done"}
    - tag  ∈ Nat (monotone return-location marker)
*)

CONSTANTS Proc, PC
Proc == {"Even", "Odd"}
PC   == {"enter","waiting","done"}

U == "U"

Complement(p) == IF p = "Even" THEN "Odd" ELSE "Even"
IsEven(n)     == (n % 2) = 0

FrameType == [proc: Proc, arg: Nat, pc: PC, tag: Nat]

Top(s) == s[Len(s)]

ReplaceTop(s, f) ==
  [ i \in 1..Len(s) |-> IF i = Len(s) THEN f ELSE s[i] ]

VARIABLES stack, res, nextTag

Vars == << stack, res, nextTag >>

Init ==
  /\ stack = << [proc |-> "Even", arg |-> N, pc |-> "enter", tag |-> 0] >>
  /\ res = U
  /\ nextTag = 1

Terminated == /\ stack = <<>> /\ res \in BOOLEAN

(*
  Enter action:
    - If top.pc = "enter" and top.arg = 0, set base-case result and mark frame done.
    - If top.pc = "enter" and top.arg > 0, set caller to waiting and push callee with arg-1.
*)
Enter ==
  /\ stack # <<>>
  /\ LET i == Len(stack) IN
     LET top == stack[i] IN
       /\ top.pc = "enter"
       /\ IF top.arg = 0 THEN
            /\ stack' = ReplaceTop(stack, [top EXCEPT !.pc = "done"])
            /\ res'   = IF top.proc = "Even" THEN TRUE ELSE FALSE
            /\ nextTag' = nextTag
          ELSE
            LET caller' == [top EXCEPT !.pc = "waiting"] IN
            LET new == [proc |-> Complement(top.proc),
                        arg  |-> top.arg - 1,
                        pc   |-> "enter",
                        tag  |-> nextTag] IN
              /\ stack' = Append(ReplaceTop(stack, caller'), new)
              /\ res' = res
              /\ nextTag' = nextTag + 1

(*
  Return action:
    - If top.pc = "done", pop it; if a parent exists, mark the parent as done.
    - Result is already determined at the base case; returns only unwind.
*)
Return ==
  /\ stack # <<>>
  /\ LET i == Len(stack) IN
     LET top == stack[i] IN
       /\ top.pc = "done"
       /\ IF i = 1 THEN
            /\ stack' = <<>>
            /\ res' = res
            /\ nextTag' = nextTag
          ELSE
            LET parent == stack[i-1] IN
            LET parent' == [parent EXCEPT !.pc = "done"] IN
            LET s1 == [ j \in 1..(i-1)
                        |-> IF j = i-1 THEN parent' ELSE stack[j] ] IN
              /\ stack' = s1
              /\ res' = res
              /\ nextTag' = nextTag

(*
  No further steps once Terminated; otherwise, either Enter or Return applies.
*)
Next ==
  IF Terminated
    THEN UNCHANGED Vars
    ELSE Enter \/ Return

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Enter)
  /\ WF_Vars(Return)

(*
  Safety invariants
*)
OnlyTopMayEnter ==
  /\ Len(stack) = 0
     \/ \A j \in 1..Len(stack)-1 : stack[j].pc # "enter"

TopNotWaiting ==
  /\ Len(stack) = 0
     \/ stack[Len(stack)].pc \in {"enter","done"}

ReturnTagsStrictlyIncrease ==
  \A i, j \in 1..Len(stack) : i < j => stack[i].tag < stack[j].tag

TypeInv ==
  /\ res \in BOOLEAN \cup {U}
  /\ stack \in Seq(FrameType)
  /\ OnlyTopMayEnter
  /\ TopNotWaiting
  /\ ReturnTagsStrictlyIncrease

FunctionalCorrectness ==
  Terminated => (res = IsEven(N))

StackCleanOnTermination ==
  Terminated => (stack = <<>>)

Safety ==
  TypeInv /\ FunctionalCorrectness /\ StackCleanOnTermination

(*
  Liveness: every behavior of Spec eventually terminates.
*)
Termination ==
  Spec => <>Terminated

=============================================================================