---- MODULE ProgramCalls ----
EXTENDS Naturals, Sequences

CONSTANTS

(* A default value used to initialize variables; bound by the configuration. *)
defaultInitValue

VARIABLES pc, m, rv, Stack, AddLocals, ToStrLocals, out

(*
  Immediate arguments for the adder, expected integer result, and expected string.
  The main sequence computes 2 + 3 = 5 and expects "5".
*)
A1 == 2
A2 == 3
ExpectedInt == A1 + A2
ExpectedString == "5"

(*
  Call stack utilities for sequences treated as stacks with top at the tail.
*)
Top(s) == s[Len(s)]
Pop(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)
Push(s, f) == Append(s, f)

(*
  Initial state:
  - pc at "Start"
  - locals and return value set to defaultInitValue
  - output set to defaultInitValue
  - empty stack
  - callee locals set to defaultInitValue
*)
Init ==
  /\ pc = "Start"
  /\ m = [resAdd |-> defaultInitValue, resStr |-> defaultInitValue]
  /\ rv = defaultInitValue
  /\ out = defaultInitValue
  /\ Stack = << >>
  /\ AddLocals = [a |-> defaultInitValue, b |-> defaultInitValue]
  /\ ToStrLocals = [n |-> defaultInitValue]

(*
  Main calls Add with immediate integer arguments.
  Pushes a frame with a saved return location and saved caller locals.
*)
Main_CallAdd ==
  /\ pc = "Start"
  /\ Stack' = Push(Stack, [retPc |-> "AfterAdd", savedLocals |-> m])
  /\ AddLocals' = [a |-> A1, b |-> A2]
  /\ pc' = "InAdd"
  /\ UNCHANGED << m, rv, ToStrLocals, out >>

(*
  Adder procedure computes return value and pops the frame to resume the caller,
  restoring caller locals.
*)
Add_Return ==
  /\ pc = "InAdd"
  /\ Len(Stack) > 0
  /\ LET fr == Top(Stack) IN
       /\ rv' = AddLocals.a + AddLocals.b
       /\ m' = fr.savedLocals
       /\ pc' = fr.retPc
       /\ Stack' = Pop(Stack)
  /\ UNCHANGED << AddLocals, ToStrLocals, out >>

(*
  Main passes the Add result into ToStr. It updates a local to record the
  integer result and then calls ToStr, pushing a new frame.
*)
Main_CallToStr ==
  /\ pc = "AfterAdd"
  /\ LET m1 == [m EXCEPT !.resAdd = rv] IN
       /\ m' = m1
       /\ Stack' = Push(Stack, [retPc |-> "AfterToStr", savedLocals |-> m1])
       /\ ToStrLocals' = [n |-> rv]
       /\ pc' = "InToStr"
  /\ UNCHANGED << AddLocals, rv, out >>

(*
  ToStr procedure only handles ExpectedInt; this models an assertion that fails
  if invoked on any other integer by disabling the action otherwise.
  It computes the return value (ExpectedString), pops the stack, and resumes caller.
*)
ToStr_Return ==
  /\ pc = "InToStr"
  /\ ToStrLocals.n = ExpectedInt
  /\ Len(Stack) > 0
  /\ LET fr == Top(Stack) IN
       /\ rv' = ExpectedString
       /\ m' = fr.savedLocals
       /\ pc' = fr.retPc
       /\ Stack' = Pop(Stack)
  /\ UNCHANGED << AddLocals, ToStrLocals, out >>

(*
  Main records the returned string into the global output, and stores it in a local.
*)
Main_RecordOut ==
  /\ pc = "AfterToStr"
  /\ m' = [m EXCEPT !.resStr = rv]
  /\ out' = rv
  /\ pc' = "Assert"
  /\ UNCHANGED << Stack, AddLocals, ToStrLocals, rv >>

(*
  Main asserts that the final output equals the expected string and then finishes.
  The assertion is modeled by requiring the equality to hold for the step to be enabled.
*)
Main_Assert ==
  /\ pc = "Assert"
  /\ out = ExpectedString
  /\ pc' = "Done"
  /\ UNCHANGED << Stack, m, AddLocals, ToStrLocals, rv, out >>

Next ==
  Main_CallAdd
  \/ Add_Return
  \/ Main_CallToStr
  \/ ToStr_Return
  \/ Main_RecordOut
  \/ Main_Assert

vars == << pc, m, rv, Stack, AddLocals, ToStrLocals, out >>

(*
  Termination (terminal state) and properties.
*)
Terminated == pc = "Done" /\ Stack = << >>
Safety == [](Terminated => out = ExpectedString)
Liveness == <>Terminated

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Main_CallAdd)
  /\ WF_vars(Add_Return)
  /\ WF_vars(Main_CallToStr)
  /\ WF_vars(ToStr_Return)
  /\ WF_vars(Main_RecordOut)
  /\ WF_vars(Main_Assert)

====