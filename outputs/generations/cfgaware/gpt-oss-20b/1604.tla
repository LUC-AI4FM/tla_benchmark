MODULE ProcedureCallSpec
IMPORTS Integers, Sequences

CONSTANT defaultInitValue

VARIABLES pc, stack, locals

IntToString(n) == IF n = 10 THEN "10" ELSE "?"

(* --- Initial state ----------------------------------------------------- *)
Init ==
    /\ pc = 0
    /\ stack = <<>>
    /\ locals = [x |-> defaultInitValue,
                 y |-> defaultInitValue,
                 s |-> ""]
    /\ TRUE

(* --- Actions ----------------------------------------------------------- *)

MainStart ==
    /\ pc = 0
    /\ locals' = [locals EXCEPT !.x = 5]
    /\ pc' = 1
    /\ stack' = stack

CallAddProc ==
    /\ pc = 1
    /\ LET frame == [proc |-> "AddProc",
                     retPc |-> 4,
                     locals |-> locals] IN
       stack' = Append(stack, frame)
    /\ pc' = 2
    /\ locals' = locals

AddBody ==
    /\ pc = 2
    /\ locals' = [locals EXCEPT !.y = locals.x + locals.x]
    /\ pc' = 3
    /\ stack' = stack

ReturnFromAdd ==
    /\ pc = 3
    /\ Len(stack) > 0
    /\ LET top == Last(stack) IN
       pc' = top.retPc
       /\ locals' = top.locals
       /\ stack' = SubSeq(stack, 1, Len(stack)-1)

CallToString ==
    /\ pc = 4
    /\ LET frame == [proc |-> "ToStringProc",
                     retPc |-> 7,
                     locals |-> locals] IN
       stack' = Append(stack, frame)
    /\ pc' = 5
    /\ locals' = locals

ToStringBody ==
    /\ pc = 5
    /\ locals' = [locals EXCEPT !.s = IntToString(locals.y)]
    /\ pc' = 6
    /\ stack' = stack

ReturnFromToString ==
    /\ pc = 6
    /\ Len(stack) > 0
    /\ LET top == Last(stack) IN
       pc' = top.retPc
       /\ locals' = top.locals
       /\ stack' = SubSeq(stack, 1, Len(stack)-1)

Done ==
    /\ pc = 7
    /\ UNCHANGED <<pc, stack, locals>>

Next == MainStart \/ CallAddProc \/ AddBody \/ ReturnFromAdd
        \/ CallToString \/ ToStringBody \/ ReturnFromToString \/ Done

(* --- Assertions -------------------------------------------------------- *)
Inv ==
    /\ IF pc = 5 THEN locals