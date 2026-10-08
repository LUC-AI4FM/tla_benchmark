------------------------------ MODULE PlusCalProgram ------------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES pc, stack, val, outStr

TenString == << "1", "0" >>

Init ==
  /\ pc = 0
  /\ stack = << >>
  /\ val = 0
  /\ outStr = << >>

CallAdd ==
  /\ pc = 0
  /\ stack' = Append(stack, 4)
  /\ pc' = 1

DoAddAndReturn ==
  /\ pc = 1
  /\ Len(stack) > 0
  /\ val' = 10
  /\ stack' = << >>
  /\ pc' = 4

CallIntToStr ==
  /\ pc = 4
  /\ stack' = Append(stack, 6)
  /\ pc' = 5

DoConvertAndReturn ==
  /\ pc = 5
  /\ Len(stack) > 0
  /\ outStr' = TenString
  /\ stack' = << >>
  /\ pc' = 6

FinalState ==
  /\ pc = 6
  /\ UNCHANGED << stack, val, outStr >>

Next == CallAdd \/ DoAddAndReturn \/ CallIntToStr \/ DoConvertAndReturn \/ FinalState

SafetyInv == 
  /\ (pc = 5 => val = 10)
  /\ (pc = 6 => outStr = TenString)

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ [] SafetyInv
  /\ <> (pc = 6)

=============================================================================