---------------------------- MODULE ProcReturn ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

(* --algorithm ProcReturn
variables ret = 0, output = "";

procedure add(a, b)
begin
  Add:
    ret := a + b;
    return;
end procedure;

procedure toString(n)
begin
  ToStr:
    if n = 10 then
      ret := "10";
    else
      ret := "unknown";
    end if;
    return;
end procedure;

begin
  CallAdd:
    call add(3, 7);
  CheckAdd:
    assert ret = 10;
    call toString(ret);
  Store:
    assert ret = "10";
    output := ret;
  Check:
    assert output = "10";
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES ret, output, pc, stack, a, b, n

vars == << ret, output, pc, stack, a, b, n >>

Init == (* Global variables *)
        /\ ret = 0
        /\ output = ""
        (* Procedure add *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        (* Procedure toString *)
        /\ n = defaultInitValue
        /\ stack = << >>
        /\ pc = "CallAdd"

Add == /\ pc = "Add"
       /\ ret' = a + b
       /\ pc' = Head(stack).pc
       /\ a' = Head(stack).a
       /\ b' = Head(stack).b
       /\ stack' = Tail(stack)
       /\ UNCHANGED << output, n >>

add == Add

ToStr == /\ pc = "ToStr"
         /\ IF n = 10
               THEN /\ ret' = "10"
               ELSE /\ ret' = "unknown"
         /\ pc' = Head(stack).pc
         /\ n' = Head(stack).n
         /\ stack' = Tail(stack)
         /\ UNCHANGED << output, a, b >>

toString == ToStr

CallAdd == /\ pc = "CallAdd"
           /\ /\ a' = 3
              /\ b' = 7
              /\ stack' = << [ procedure |->  "add",
                               pc        |->  "CheckAdd",
                               a         |->  a,
                               b         |->  b ] >>
                           \o stack
           /\ pc' = "Add"
           /\ UNCHANGED << ret, output, n >>

CheckAdd == /\ pc = "CheckAdd"
            /\ Assert(ret = 10,
                      "Failure of assertion at line 30, column 5.")
            /\ /\ n' = ret
               /\ stack' = << [ procedure |->  "toString",
                                pc        |->  "Store",
                                n         |->  n ] >>
                            \o stack
            /\ pc' = "ToStr"
            /\ UNCHANGED << ret, output, a, b >>

Store == /\ pc = "Store"
         /\ Assert(ret = "10",
                   "Failure of assertion at line 33, column 5.")
         /\ output' = ret
         /\ pc' = "Check"
         /\ UNCHANGED << ret, stack, a, b, n >>

Check == /\ pc = "Check"
         /\ Assert(output = "10",
                   "Failure of assertion at line 36, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED << ret, output, stack, a, b, n >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == add \/ toString \/ CallAdd \/ CheckAdd \/ Store \/ Check
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================