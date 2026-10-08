------------------------------ MODULE EvenOdd ------------------------------

EXTENDS Naturals, Sequences

CONSTANT N

ASSUME N \in Nat

VARIABLES pc, result, stack, xEven, xOdd

(*
PlusCal sketch (for documentation only):

--algorithm EvenOdd
variables result = FALSE;

procedure Even(x) ;
begin
EvenEnter:
  if x = 0 then
    result := TRUE;
  else
EvenBeforeCallOdd:
    call Odd(x - 1);
  end if;
EvenAfterCall:
  return;
end procedure;

procedure Odd(x) ;
begin
OddEnter:
  if x = 0 then
    result := FALSE;
  else
OddBeforeCallEven:
    call Even(x - 1);
  end if;
OddAfterCall:
  return;
end procedure;

begin
MainStart:
  call Even(N);
Done:
  print result;
end algorithm
*)

vars == << pc, stack, result, xEven, xOdd >>

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)

Init ==
  /\ pc = "MainStart"
  /\ result = FALSE
  /\ stack = << >>
  /\ xEven \in Nat
  /\ xOdd \in Nat

InOdd == pc = "OddEnter"
CallOdd == pc = "EvenBeforeCallOdd"

MainCall ==
  LET f == [proc |-> "Even", x |-> N, fpc |-> "EvenEnter"]
  IN
    /\ pc = "MainStart"
    /\ stack' = << f >>
    /\ xEven' = N
    /\ xOdd' = xOdd
    /\ result' = result
    /\ pc' = "EvenEnter"

EvenBase ==
  LET s2 == Pop(stack)
  IN
    /\ pc = "EvenEnter"
    /\ Len(stack) > 0
    /\ Top(stack).proc = "Even"
    /\ xEven = Top(stack).x
    /\ xEven = 0
    /\ result' = TRUE
    /\ xEven' = xEven
    /\ xOdd' = xOdd
    /\ stack' = s2
    /\ pc' = IF Len(s2) = 0 THEN "Done" ELSE Top(s2).fpc

EvenPrepCall ==
  /\ pc = "EvenEnter"
  /\ Len(stack) > 0
  /\ Top(stack).proc = "Even"
  /\ xEven = Top(stack).x
  /\ xEven > 0
  /\ pc' = "EvenBeforeCallOdd"
  /\ UNCHANGED << stack, result, xEven, xOdd >>

EvenCallOdd ==
  LET s1 == [stack EXCEPT ![Len(stack)].fpc = "EvenAfterCall"]
  IN
    /\ pc = "EvenBeforeCallOdd"
    /\ Len(stack) > 0
    /\ Top(stack).proc = "Even"
    /\ xEven = Top(stack).x
    /\ xEven > 0
    /\ stack' = Append(s1, [proc |-> "Odd", x |-> xEven - 1, fpc |-> "OddEnter"])
    /\ xOdd' = xEven - 1
    /\ xEven' = xEven
    /\ result' = result
    /\ pc' = "OddEnter"

OddBase ==
  LET s2 == Pop(stack)
  IN
    /\ pc = "OddEnter"
    /\ Len(stack) > 0
    /\ Top(stack).proc = "Odd"
    /\ xOdd = Top(stack).x
    /\ xOdd = 0
    /\ result' = FALSE
    /\ xEven' = xEven
    /\ xOdd' = xOdd
    /\ stack' = s2
    /\ pc' = IF Len(s2) = 0 THEN "Done" ELSE Top(s2).fpc

OddPrepCall ==
  /\ pc = "OddEnter"
  /\ Len(stack) > 0
  /\ Top(stack).proc = "Odd"
  /\ xOdd = Top(stack).x
  /\ xOdd > 0
  /\ pc' = "OddBeforeCallEven"
  /\ UNCHANGED << stack, result, xEven, xOdd >>

OddCallEven ==
  LET s1 == [stack EXCEPT ![Len(stack)].fpc = "OddAfterCall"]
  IN
    /\ pc = "OddBeforeCallEven"
    /\ Len(stack) > 0
    /\ Top(stack).proc = "Odd"
    /\ xOdd = Top(stack).x
    /\ xOdd > 0
    /\ stack' = Append(s1, [proc |-> "Even", x |-> xOdd - 1, fpc |-> "EvenEnter"])
    /\ xEven' = xOdd - 1
    /\ xOdd' = xOdd
    /\ result' = result
    /\ pc' = "EvenEnter"

EvenReturn ==
  LET s2 == Pop(stack)
  IN
    /\ pc = "EvenAfterCall"
    /\ Len(stack) > 0
    /\ Top(stack).proc = "Even"
    /\ stack' = s2
    /\ pc' = IF Len(s2) = 0 THEN "Done" ELSE Top(s2).fpc
    /\ xEven' = xEven
    /\ xOdd' = xOdd
    /\ result' = result

OddReturn ==
  LET s2 == Pop(stack)
  IN
    /\ pc = "OddAfterCall"
    /\ Len(stack) > 0
    /\ Top(stack).proc = "Odd"
    /\ stack' = s2
    /\ pc' = IF Len(s2) = 0 THEN "Done" ELSE Top(s2).fpc
    /\ xEven' = xEven
    /\ xOdd' = xOdd
    /\ result' = result

Next ==
    MainCall
  \/ EvenBase
  \/ EvenPrepCall
  \/ EvenCallOdd
  \/ OddBase
  \/ OddPrepCall
  \/ OddCallEven
  \/ EvenReturn
  \/ OddReturn

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

============================================================================