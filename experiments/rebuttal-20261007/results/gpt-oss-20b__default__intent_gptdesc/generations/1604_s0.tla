MODULE CallStackSpec
EXTENDS Naturals, Sequences, Integers

CONSTANTS X, Y, EXPECTED_INT, EXPECTED_STRING

VARIABLES stack, addX, addY, addResult, convInput, output, done

vars == <<stack, addX, addY, addResult, convInput, output, done>>

Init ==
  /\ stack = <<>>
  /\ addX = 0
  /\ addY = 0
  /\ addResult = 0
  /\ convInput = 0
  /\ output = ""
  /\ done = FALSE

Frame == [proc : STRING]

MainInvokeAdd ==
  /\ Len(stack) = 0
  /\ addX' = X
  /\ addY' = Y
  /\ stack' = Append(stack, [proc |-> "Add"])
  /\ UNCHANGED <<addResult, convInput, output, done>>

AddCompute ==
  /\ Len(stack) > 0
  /\ Last(stack).proc = "Add"
  /\ addResult' = addX + addY
  /\ stack' = SubSeq(stack, 1, Len(stack)-1)
  /\ UNCHANGED <<addX, addY, convInput, output, done>>

AfterAdd ==
  /\ Len(stack) = 0
  /\ convInput' = addResult
  /\ stack' = Append(stack, [proc |-> "Conv"])
  /\ UNCHANGED <<addX, addY, addResult, output, done>>

ConvCompute ==
  /\ Len(stack) > 0
  /\ Last(stack).proc = "Conv"
  /\ convInput = EXPECTED_INT
  /\ output' = ToStr[convInput]
  /\ stack' = SubSeq(stack, 1, Len(stack)-1)
  /\ UNCHANGED <<addX, addY, addResult, convInput, done>>

AfterConv ==
  /\ Len(stack) = 0
  /\ done' = TRUE
  /\ UNCHANGED <<addX, addY, addResult, convInput, output>>

ToStr == [i \in Int |-> IF i = EXPECTED_INT THEN EXPECTED_STRING ELSE ""]

Next == MainInvokeAdd \/ AddCompute \/ AfterAdd \/ ConvCompute \/ AfterConv

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

SafetyInvariant == [] (done => output = EXPECTED_STRING)
LivenessProperty == <> done

THEOREM SpecImpliesSafety : Spec => SafetyInvariant
THEOREM SpecImpliesLiveness : Spec => LivenessProperty

END CallStackSpec