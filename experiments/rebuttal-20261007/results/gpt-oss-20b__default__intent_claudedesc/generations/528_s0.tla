MODULE Demo
EXTENDS Naturals, Sequences, TLC

(*--algorithm Demo
variables s, seq, finished

begin
  s := {"a", "b"};
  seq := <<1,2,3>>;
  finished := FALSE;

  s := s \cup {"c"};
  print "Updated set: ", s;

  seq[2] := 42;
  print "Updated sequence: ", seq;

  finished := TRUE;
end
--*)

Inv == s \subseteq {"a", "b", "c"}

Spec == Init /\ [][Next]_vars

Liveness == <> finished

THEOREM Spec => [] Inv
THEOREM Spec => Liveness