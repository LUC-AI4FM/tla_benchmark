MODULE EvenOdd
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES stack, res, pc

(* Record representing an activation record *)
Frame == [proc : {"Even","Odd"}, arg : Nat, loc : 
          {"EStart","EReturnTrue","EAfterOdd",
           "OStart","OReturnFalse","OAfterEven"}]

TopFrame(s) == FIRST(s)
RestStack(s) == Tail(s)

(* Update the location of the top frame in a stack *)
UpdateTopLoc(s, newLoc) ==
  LET top == FIRST(s)
      rest == Tail(s)
  IN rest \o << [top EXCEPT !.loc = newLoc] >>

(* Compute pc from a stack *)
PcFromStack(s) ==
  IF Len(s)=0 THEN "Done"
  ELSE (First(s)).proc \o "_" \o (First(s)).loc

Init ==
  /\ stack = << [proc |-> "Even", arg |-> N, loc |-> "EStart"] >>
  /\ res   = FALSE
  /\ pc    = PcFromStack(stack)

(* Transition when Even calls Odd *)
CallOdd ==
  LET top == TopFrame(stack)
      rest == RestStack(stack)
  IN /\ top.proc   = "Even"
     /\ top.loc    = "EStart"
     /\ top.arg # 0
     /\ LET newArg == top.arg - 1 IN
        /\ stack' = UpdateTopLoc(stack, "EAfterOdd") \o <<
                      [proc |-> "Odd", arg |-> newArg, loc |-> "OStart"] >>
        /\ res'   = res
        /\ pc'    = PcFromStack(stack')

(* Transition when Odd calls Even *)
CallEven ==
  LET top == TopFrame(stack)
      rest == RestStack(stack)
  IN /\ top.proc   = "Odd"
     /\ top.loc    = "OStart"
     /\ top.arg # 0
     /\ LET newArg == top.arg - 1 IN
        /\ stack' = UpdateTopLoc(stack, "OAfterEven") \o <<
                      [proc |-> "Even", arg |-> newArg, loc |-> "EStart"] >>
        /\ res'   = res
        /\ pc'    = PcFromStack(stack')

(* Even returns true when argument is 0 *)
EReturnTrue ==
  LET top == TopFrame(stack)
      rest == RestStack(stack)
  IN /\ top.proc = "Even"
     /\ top.loc  = "EStart"
     /\ top.arg  = 0
     /\ res'   = TRUE
     /\ stack' = rest
     /\ pc'    = PcFromStack(stack')

(* Odd returns false when argument is 0 *)
OReturnFalse ==
  LET top == TopFrame(stack)
      rest == RestStack(stack)
  IN /\ top.proc = "Odd"
     /\ top.loc  = "OStart"
     /\ top.arg  = 0
     /\ res'   = FALSE
     /\ stack' = rest
     /\ pc'    = PcFromStack(stack')

(* Even receives result from Odd and inverts it *)
EAfterOdd ==
  LET top == TopFrame(stack)
      rest == RestStack(stack)
  IN /\ top.proc = "Even"
     /\ top.loc  = "EAfterOdd"
     /\ res'   = NOT res
     /\ stack' = rest
     /\ pc'    = PcFromStack(stack')

(* Odd receives result from Even and inverts it *)
OAfterEven ==
  LET top == TopFrame(stack)
      rest == RestStack(stack)
  IN /\ top.proc = "Odd"
     /\ top.loc  = "OAfterEven"
     /\ res'   = NOT res
     /\ stack' = rest
     /\ pc'    = PcFromStack(stack')

(* Stuttering step *)
Stutter ==
  /\ pc'    = pc
  /\ stack' = stack
  /\ res'   = res

Next == CallOdd \/ CallEven \/ EReturnTrue \/ OReturnFalse
          \/ EAfterOdd \/ OAfterEven \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

THEOREM EvenOddTermination IS
  Spec => Termination
====================================================================