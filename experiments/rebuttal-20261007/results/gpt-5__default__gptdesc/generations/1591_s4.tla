----------------------------- MODULE EvenOdd -----------------------------

EXTENDS Naturals, Sequences

CONSTANT N
ASSUME N \in Nat

(*
  This module specifies a PlusCal-style mutual recursion between procedures
  Even and Odd using an explicit program counter, an explicit call stack of
  activation records, and per-procedure local variables xEven and xOdd.
*)

CONSTANTS

VARIABLES pc, stack, xEven, xOdd, result

Procs == {"Even", "Odd"}
Locs  == {"enter", "wait", "after"}
PCVals == {"Start", "Run", "Done"}
NoVal == "NoVal"

FrameSet == [proc: Procs, n: Nat, loc: Locs, ret: BOOLEAN \cup {NoVal}]

vars == << pc, stack, xEven, xOdd, result >>

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = [i \in Nat |-> 0]
  /\ xOdd  = [i \in Nat |-> 0]
  /\ result \in BOOLEAN

StartStep ==
  /\ pc = "Start"
  /\ stack' = << [proc |-> "Even", n |-> N, loc |-> "enter", ret |-> NoVal] >>
  /\ pc' = "Run"
  /\ UNCHANGED << xEven, xOdd, result >>

EvenZero ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET i == Len(stack) IN
     /\ stack[i].proc = "Even"
     /\ stack[i].loc = "enter"
     /\ stack[i].n = 0
     /\ stack' = [stack EXCEPT ![i] = [@ EXCEPT !.ret = TRUE, !.loc = "after"]]
  /\ UNCHANGED << pc, xEven, xOdd, result >>

OddZero ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET i == Len(stack) IN
     /\ stack[i].proc = "Odd"
     /\ stack[i].loc = "enter"
     /\ stack[i].n = 0
     /\ stack' = [stack EXCEPT ![i] = [@ EXCEPT !.ret = FALSE, !.loc = "after"]]
  /\ UNCHANGED << pc, xEven, xOdd, result >>

EvenRecurse ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET i == Len(stack) IN
     /\ stack[i].proc = "Even"
     /\ stack[i].loc = "enter"
     /\ stack[i].n > 0
     /\ xEven' = [xEven EXCEPT ![i] = stack[i].n]
     /\ stack' =
          Append(
            [stack EXCEPT ![i].loc = "wait"],
            [proc |-> "Odd", n |-> stack[i].n - 1, loc |-> "enter", ret |-> NoVal]
          )
  /\ UNCHANGED << pc, xOdd, result >>

OddRecurse ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET i == Len(stack) IN
     /\ stack[i].proc = "Odd"
     /\ stack[i].loc = "enter"
     /\ stack[i].n > 0
     /\ xOdd' = [xOdd EXCEPT ![i] = stack[i].n]
     /\ stack' =
          Append(
            [stack EXCEPT ![i].loc = "wait"],
            [proc |-> "Even", n |-> stack[i].n - 1, loc |-> "enter", ret |-> NoVal]
          )
  /\ UNCHANGED << pc, xEven, result >>

ReturnStep ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET i == Len(stack) IN
     /\ stack[i].loc = "after"
     /\ stack[i].ret \in BOOLEAN
     /\ IF i = 1 THEN
           /\ stack' = << >>
           /\ pc' = "Done"
           /\ result' = stack[i].ret
           /\ UNCHANGED << xEven, xOdd >>
        ELSE
           /\ LET retv == stack[i].ret IN
              LET s1 == SubSeq(stack, 1, i - 1) IN
                /\ stack' = [s1 EXCEPT ![i - 1] = [@ EXCEPT !.ret = retv, !.loc = "after"]]
           /\ UNCHANGED << pc, xEven, xOdd, result >>

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  StartStep
  \/ EvenZero
  \/ OddZero
  \/ EvenRecurse
  \/ OddRecurse
  \/ ReturnStep
  \/ DoneStutter

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInv ==
  /\ pc \in PCVals
  /\ stack \in Seq(FrameSet)
  /\ xEven \in [Nat -> Nat]
  /\ xOdd  \in [Nat -> Nat]
  /\ result \in BOOLEAN
  /\ \A k \in 1..Len(stack): stack[k].loc = "after" => stack[k].ret \in BOOLEAN
  /\ \A k \in 1..Len(stack): stack[k].loc # "after" => stack[k].ret = NoVal

Termination ==
  <> (pc = "Done")

=============================================================================