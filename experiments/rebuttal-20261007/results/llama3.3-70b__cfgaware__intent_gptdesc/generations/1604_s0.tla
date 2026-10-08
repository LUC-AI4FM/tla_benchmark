---------------------------- MODULE AddAndConvert ----------------------------
EXTENDS Integers, Strings

CONSTANT ExpectedOutput
VARIABLE locals, returnVal, output, stack

vars == <<locals, returnVal, output, stack>>

defaultInitValue == (locals = <<0, 0>>, returnVal = 0, output = "", stack = <<>>)

Add(a, b) == a + b

ConvertToString(n) ==
  IF n = Add(2, 3)
  THEN "5"
  ELSE Assert(FALSE, "Invalid input to ConvertToString")

PushFrame(frame) == stack' = Append(stack, frame)

PopFrame() == stack' = SubSeq(stack, 1, Len(stack))

CallAdd(a, b) ==
  /\ PushFrame(<<<<"add">>, <<a, b>>, 0>>)
  /\ locals' = <<a, b>>
  /\ UNCHANGED returnVal
  /\ UNCHANGED output

ReturnFromAdd() ==
  /\ PopFrame()
  /\ returnVal' = Add(locals[1], locals[2])
  /\ locals' = defaultInitValue.locals
  /\ UNCHANGED output

CallConvertToString(n) ==
  /\ PushFrame(<<<<"convert">>, <<n>>, 0>>)
  /\ locals' = <<n>>
  /\ UNCHANGED returnVal
  /\ UNCHANGED output

ReturnFromConvertToString() ==
  /\ PopFrame()
  /\ output' = ConvertToString(locals[1])
  /\ locals' = defaultInitValue.locals
  /\ UNCHANGED returnVal

MainStep == 
  \/ (stack = <<>> /\ CallAdd(2, 3))
  \/ (stack # <<>> /\ stack[Len(stack)][1] = "add" /\ ReturnFromAdd())
  \/ (stack # <<>> /\ stack[Len(stack)][1] = "convert" /\ ReturnFromConvertToString())

Spec == 
  /\ defaultInitValue
  /\ [][MainStep]_vars
  /\ WF_vars(MainStep)

THEOREM Spec => []<>(output = ExpectedOutput)
THEOREM Spec => <>[](stack = <<>>)
=============================================================================