------------------------------- MODULE EvenOdd -------------------------------

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

(*--algorithm EvenOdd
variables xEven = 0, xOdd = 0, result = FALSE;

procedure Even(n)
begin
    if n = 0 then
        result := TRUE;
        return;
    else
        call Odd(n - 1);
    end if;
end procedure;

procedure Odd(n)
begin
    if n = 0 then
        result := FALSE;
        return;
    else
        call Even(n - 1);
    end if;
end procedure;

begin
    call Even(N);
    pc := "Done";
end algorithm;*)

Init == 
    /\ pc = "Even"
    /\ stack = <<>>
    /\ xEven = N
    /\ xOdd = 0
    /\ result = FALSE

Next ==
    \/ \* In Even procedure
       (pc = "Even" /\ xEven = 0 /\ UNCHANGED <<stack, xOdd, result>> /\ pc' = "Done")
    \/ (pc = "Even" /\ xEven # 0 /\ stack' = Append(stack, <<pc, xEven>>) /\ pc' = "Odd" /\ xOdd' = xEven - 1 /\ UNCHANGED <<xEven, result>>)
    \/ \* In Odd procedure
       (pc = "Odd" /\ xOdd = 0 /\ UNCHANGED <<stack, xEven, result>> /\ pc' = "Done")
    \/ (pc = "Odd" /\ xOdd # 0 /\ stack' = Append(stack, <<pc, xOdd>>) /\ pc' = "Even" /\ xEven' = xOdd - 1 /\ UNCHANGED <<xOdd, result>>)
    \/ \* Return from procedure
       (\E top \in stack : 
            (top[1] = "Even" /\ pc = "Done" /\ LET prevPc == top[1], prevX == top[2] IN
                stack' = Tail(stack) /\ pc' = prevPc /\ xOdd' = prevX /\ result' = result)
        \/ (top[1] = "Odd" /\ pc = "Done" /\ LET prevPc == top[1], prevX == top[2] IN
                stack' = Tail(stack) /\ pc' = prevPc /\ xEven' = prevX /\ result' = result))

Spec ==
    /\ Init
    /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
    /\ WF_next(Next)

Termination ==
    <>(pc = "Done")

=============================================================================