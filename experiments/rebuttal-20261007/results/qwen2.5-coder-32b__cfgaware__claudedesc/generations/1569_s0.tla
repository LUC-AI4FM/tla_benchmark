------------------------------- MODULE CBakery -------------------------------

CONSTANTS NumProcs, MaxNum

VARIABLES num, choosing

(*--algorithm bakery
variables num = [p \in 1..NumProcs |-> 0],
          choosing = [p \in 1..NumProcs |-> FALSE];

process p \in 1..NumProcs
begin
d1:   choosing[p] := TRUE;
d2:   max \in 0..MaxNum;
      with (max)
         \E q \in 1..NumProcs : max = num[q];
      nxt \in 0..MaxNum;
      nxt := max + 1;
      read \in 0..MaxNum;
      read := nxt;
      num[p] := read;
d3:   choosing[p] := FALSE;
w1:   while \E q \in 1..NumProcs : (choosing[q] \/ 
                                     (num[q] # 0 /\ 
                                      ((num[q] < num[p]) \/ 
                                       (num[q] = num[p] /\ q < p))))
    do
w2:      skip;
cs:   assert \A q \in 1..NumProcs \ {p} : num[q] = 0;
       num[p] := 0;
end process;

end algorithm *)

Init == \/ num = [p \in 1..NumProcs |-> 0]
        /\ choosing = [p \in 1..NumProcs |-> FALSE]

Next ==
    \E p \in 1..NumProcs :
      \/ \/ choosing[p] = FALSE
             /\ \/ \E q \in 1..NumProcs : (choosing[q] \/ 
                                            (num[q] # 0 /\ 
                                             ((num[q] < num[p]) \/ 
                                              (num[q] = num[p] /\ q < p))))
                \/ choosing' = [choosing EXCEPT ![p] = TRUE]
                   /\ \E max \in 0..MaxNum :
                      \E nxt \in 0..MaxNum :
                         \A q \in 1..NumProcs : (max >= num[q])
                         /\ nxt = max + 1
                         /\ num' = [num EXCEPT ![p] = nxt]
          \/ choosing[p] = TRUE
             /\ num[p] # 0
             /\ choosing' = [choosing EXCEPT ![p] = FALSE]
          \/ choosing[p] = FALSE
             /\ num[p] = 0

Spec == Init /\ [][Next]_<<num, choosing>>

Invariant ==
    \A p1, p2 \in 1..NumProcs :
      p1 # p2 => ~ (choosing[p1] \/ choosing[p2]
                    \/ (num[p1] # 0 /\ num[p2] # 0
                        /\ ((num[p1] < num[p2]) \/ 
                            (num[p1] = num[p2] /\ p1 < p2))))

=============================================================================