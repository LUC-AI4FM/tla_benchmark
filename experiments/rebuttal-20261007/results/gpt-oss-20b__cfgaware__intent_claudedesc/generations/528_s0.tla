------------------------------ MODULE IntroDemo ------------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES s, seq, done

/* --algorithm IntroDemo
variables s, seq, done;

Init == 
  /\ s = {"a", "b"}
  /\ seq = <<1,2,3>>
  /\ done = FALSE

action1 ==
  LET newSet == s \cup {"c"} IN
    PRINT "After adding 'c' to set: ", newSet;
    s := newSet;

action2 ==
  LET newSeq == Subst(seq, 2, 5) IN
    PRINT "After replacing seq[2] with 5: ", newSeq;
    seq := newSeq;

doneAction ==
  done := TRUE;

begin
  action1;
  action2;
  doneAction;
end algorithm; */

Spec == Init /\ [][Next]_vars

=============================================================================