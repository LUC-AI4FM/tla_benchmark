------------------------------- MODULE Playground -------------------------------

CONSTANTS
    \* Constants to be defined by the configuration
    Spec,
    defaultInitValue

VARIABLES
    retval,
    output,
    stack,
    pc

\* Procedures and their behavior
PROCEDURE add(x, y)
    BEGIN
        retval := x + y;
        stack := Tail(stack);
    END;

PROCEDURE to_string(n)
    BEGIN
        ASSERT n = 10;
        retval := "10";
        stack := Tail(stack);
    END;

\* Main process logic
PROCESS main = "main"
BEGIN
    retval := defaultInitValue;
    output := defaultInitValue;
    stack := << >>;
    pc := "start";

    while pc # "Done" do
        either
            \* Call add(3, 7)
            if pc = "start" then
                stack := Append(stack, "add_return");
                pc := "call_add";
            end if;

            \* Return from add
            if pc = "call_add" then
                call add(3, 7);
                pc := "after_add";
            end if;

            \* Call to_string(retval)
            if pc = "after_add" then
                stack := Append(stack, "to_string_return");
                pc := "call_to_string";
            end if;

            \* Return from to_string
            if pc = "call_to_string" then
                call to_string(retval);
                pc := "after_to_string";
            end if;

            \* Copy retval to output and assert final value
            if pc = "after_to_string" then
                output := retval;
                ASSERT output = "10";
                pc := "Done";
            end if;
        or
            \* Handle returns from procedures
            if Head(stack) = "add_return" then
                stack := Tail(stack);
                pc := "after_add";
            end if;

            if Head(stack) = "to_string_return" then
                stack := Tail(stack);
                pc := "after_to_string";
            end if;
        end either;
    end while;
END PROCESS

\* Initial predicate
Init == /\ retval = defaultInitValue
        /\ output = defaultInitValue
        /\ stack = << >>
        /\ pc = "start"

\* Next-state relation
Next == \/ \E x, y: /\ pc = "call_add"
                        /\ UNCHANGED <<retval, output>>
                        /\ stack' = Append(stack, "add_return")
                        /\ pc' = "call_add"
         \/ \E n:     /\ pc = "call_to_string"
                        /\ UNCHANGED <<retval, output>>
                        /\ stack' = Append(stack, "to_string_return")
                        /\ pc' = "call_to_string"
         \/            /\ pc = "after_add"
                        /\ retval' = 10
                        /\ UNCHANGED output
                        /\ stack' = Tail(stack)
                        /\ pc' = "after_add"
         \/            /\ pc = "after_to_string"
                        /\ retval' = "10"
                        /\ output' = retval
                        /\ ASSERT output' = "10"
                        /\ stack' = Tail(stack)
                        /\ pc' = "Done"

\* Specification
Spec == Init /\ [][Next]_<<retval, output, stack, pc>>

\* Termination property
Termination == <>(pc = "Done")

===============================================================================