------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, Temporal

CONSTANT N

VARIABLES pc, stack, result

(*--algorithm EvenOdd
variables pc = "Start", stack = <<>>, result = FALSE

procedure Even(x) {
  if x = 0 then
    result := TRUE;
  else
    Odd(x-1);
}

procedure Odd(x) {
  if x = 0 then
    result := FALSE;
  else
    Even(x-1);
}

Start:
  Even(N);
  pc := "Done";

Done:
  UNCHANGED <<pc, stack, result>>;
--*)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

====