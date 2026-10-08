------------------------------ MODULE ParityRecursive ------------------------------

EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES stack, res, ret, done

Proc  == {"Even", "Odd"}
Phase == {"Call", "Return"}
Frame == [proc: Proc, arg: Nat, phase: Phase]

Comp(p) == IF p = "Even" THEN "Odd" ELSE "Even"

RECURSIVE EvenParity(_)
EvenParity(n) == IF n = 0 THEN TRUE ELSE ~EvenParity(n - 1)

Init ==
  /\ N \in Nat
  /\ stack = << [proc |-> "Even", arg |-> N, phase |-> "Call"] >>
  /\ res \in BOOLEAN
  /\ ret \in BOOLEAN
  /\ done = FALSE

CallStep ==
  /\ ~done
  /\ Len(stack) >= 1
  /\ LET top == stack[Len(stack)] IN
       /\ top.phase = "Call"
       /\ top.arg > 0
       /\ stack' = stack \o << [proc |-> Comp(top.proc), arg |-> top.arg - 1, phase |-> "Call"] >>
  /\ UNCHANGED <<res, ret, done>>

BaseCaseStep ==
  /\ ~done
  /\ Len(stack) >= 1
  /\ LET n == Len(stack)
         top == stack[n]
     IN /\ top.phase = "Call" /\ top.arg = 0
        /\ stack' = [stack EXCEPT ![n].phase = "Return"]
        /\ ret' = IF top.proc = "Even" THEN TRUE ELSE FALSE
  /\ UNCHANGED <<res, done>>

ReturnStep ==
  /\ ~done
  /\ Len(stack) >= 1
  /\ LET n == Len(stack)
         top == stack[n]
     IN /\ top.phase = "Return"
        /\ IF n = 1
           THEN /\ stack' = << >>
                /\ res' = ret
                /\ done' = TRUE
           ELSE LET s1 == SubSeq(stack, 1, n - 1) IN
                /\ stack' = [s1 EXCEPT ![Len(@)].phase = "Return"]
                /\ UNCHANGED <<res, ret, done>>

Next == CallStep \/ BaseCaseStep \/ ReturnStep

Spec ==
  /\ Init
  /\ [][Next]_<<stack, res, ret, done>>
  /\ WF_<<stack, res, ret, done>>(CallStep)
  /\ WF_<<stack, res, ret, done>>(BaseCaseStep)
  /\ WF_<<stack, res, ret, done>>(ReturnStep)

(*
  Safety invariants: typing, stack-discipline, and correctness
*)
TypeOK ==
  /\ stack \in Seq(Frame)
  /\ res \in BOOLEAN
  /\ ret \in BOOLEAN
  /\ done \in BOOLEAN

RootInv ==
  Len(stack) = 0 \/ (stack[1].proc = "Even" /\ stack[1].arg = N)

LinkInv ==
  IF Len(stack) <= 1 THEN TRUE
  ELSE
    \A i \in 1..(Len(stack) - 1):
      /\ stack[i].arg > 0
      /\ stack[i+1].arg = stack[i].arg - 1
      /\ stack[i+1].proc = Comp(stack[i].proc)

ReturnTopOnly ==
  IF Len(stack) <= 1 THEN TRUE
  ELSE \A i \in 1..(Len(stack) - 1): stack[i].phase = "Call"

DepthBoundInv ==
  Len(stack) <= N + 1

DoneEmptyInv ==
  done <=> Len(stack) = 0

Correctness ==
  done => res = EvenParity(N)

SafetyInv ==
  TypeOK /\ RootInv /\ LinkInv /\ ReturnTopOnly /\ DepthBoundInv /\ DoneEmptyInv /\ Correctness

(*
  Liveness: termination and stability of the final result
*)
Termination ==
  <> (done /\ res = EvenParity(N))

StableAfterDone ==
  [] (done => UNCHANGED <<res, stack, ret, done>>)

=============================================================================