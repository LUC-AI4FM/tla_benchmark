---- MODULE Playground ----
EXTENDS Naturals, Sequences

(*
A small PlusCal/TLA+ playground module that models a single-process sequential
computation using two procedures with simulated return values (via a shared
global variable retval). A second global variable output holds the final result.

The process executes four labeled steps:
  1) call add(3, 7) which stores 10 in retval;
  2) call to_string(retval) which asserts its argument equals 10 and stores "10" in retval;
  3) copy retval into output;
  4) assert that output equals "10".

Procedure calls are modeled via an explicit stack variable, following PlusCal's
standard translation approach. Weak fairness is included on the main process and
both procedures. The temporal property Termination (and the equivalent Liveness
property) requires that the process eventually reaches the Done state.
*)

defaultInitValue == CHOOSE v : TRUE

CONSTANTS

VARIABLES
  pc,       \* control state of the single main process
  stack,    \* explicit call stack (a sequence of frames)
  retval,   \* global "return value" cell used by procedures
  output    \* global output holding the final result

vars == << pc, stack, retval, output >>

\* Stack frame helpers (push/pop/top)
Top(s) == s[Len(s)]
Pop(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)

\* Initial state: ready to perform the four labeled steps; empty stack; globals defaulted
Init ==
  /\ pc = "L1"
  /\ stack = << >>
  /\ retval = defaultInitValue
  /\ output = defaultInitValue

\* Main process steps (four labeled steps, plus Done stutter)
MainCallAdd ==
  /\ stack = << >>
  /\ pc = "L1"
  /\ stack' = Append(stack, [name |-> "add",
                             args |-> [a |-> 3, b |-> 7],
                             ret  |-> "L2"])
  /\ UNCHANGED << pc, retval, output >>

MainCallToString ==
  /\ stack = << >>
  /\ pc = "L2"
  /\ stack' = Append(stack, [name |-> "to_string",
                             args |-> [x |-> retval],
                             ret  |-> "L3"])
  /\ UNCHANGED << pc, retval, output >>

CopyRetval ==
  /\ stack = << >>
  /\ pc = "L3"
  /\ output' = retval
  /\ pc' = "L4"
  /\ UNCHANGED << stack, retval >>

AssertOutput ==
  /\ stack = << >>
  /\ pc = "L4"
  /\ output = "10"  \* inline assert: must hold to proceed
  /\ pc' = "Done"
  /\ UNCHANGED << stack, retval, output >>

DoneStutter ==
  /\ stack = << >>
  /\ pc = "Done"
  /\ UNCHANGED vars

MainActs == MainCallAdd \/ MainCallToString \/ CopyRetval \/ AssertOutput

\* Procedure steps implemented via the top stack frame
AddStep ==
  /\ stack # << >>
  /\ Top(stack).name = "add"
  /\ LET top == Top(stack) IN
       /\ retval' = top.args.a + top.args.b
       /\ pc' = top.ret
       /\ stack' = Pop(stack)
  /\ UNCHANGED output

ToStringStep ==
  /\ stack # << >>
  /\ Top(stack).name = "to_string"
  /\ LET top == Top(stack) IN
       /\ top.args.x = 10      \* inline assert: argument must be 10
       /\ retval' = "10"
       /\ pc' = top.ret
       /\ stack' = Pop(stack)
  /\ UNCHANGED output

ProcActs == AddStep \/ ToStringStep

Next == MainActs \/ ProcActs \/ DoneStutter

\* Spec includes weak fairness on the main process and both procedures
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(MainActs)
  /\ WF_vars(AddStep)
  /\ WF_vars(ToStringStep)

\* Liveness: eventually reach the Done state
Termination == <> (pc = "Done")
Liveness == Termination

====