------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Integers, TLC

CONSTANTS N
ASSUME N \in Nat /\ N >= 2

VARIABLES x, y, b, state, failed

(* --algorithm fast_mutual_exclusion
variables x = [p \in 1..N |-> FALSE], 
          y = [p \in 1..N |-> FALSE], 
          b = [p \in 1..N |-> FALSE], 
          state = [p \in 1..N |-> "idle"],
          failed = [p \in 1..N |-> FALSE];

process (P \in 1..N)
begin
    wait: while TRUE do
        if P = 1 then
            await: while /\ b[2] \/ x[2]
                   /\ \/ y[2] 
                      \/ b[3] \/ x[3]
                   ...
                   /\ b[N] \/ x[N]
                 do skip;
                   x[P] := TRUE;        
                   b[P] := FALSE;
        else
            await: while (\E k \in 1..N : k # P /\ (b[k] \/ x[k])) do skip;
                   y[P] := TRUE;
                   b[P] := FALSE;
        fi;

        cs: skip;

        exit: if P = 1 then
                  b[P] := TRUE; 
                  x[P] := FALSE;
              else
                  b[P] := TRUE;
                  y[P] := FALSE;
              fi;
    end while;
end process
end algorithm *)

Init == /\ x = [p \in 1..N |-> FALSE]
        /\ y = [p \in 1..N |-> FALSE]
        /\ b = [p \in 1..N |-> FALSE]
        /\ state = [p \in 1..N |-> "idle"]
        /\ failed = [p \in 1..N |-> FALSE]

Next == \/ \E P \in 1..N : \E newx, newy, newb, newstate, newfailed \in BOOLEAN: 
    (\/ P = 1 /\
          /\ (/\ b[2] \/ x[2]
             /\ \/ y[2] 
                \/ b[3] \/ x[3]
                ...
                /\ b[N] \/ x[N])
          /\ newx = [p \in 1..N |-> IF p = P THEN TRUE ELSE x[p]]
          /\ newy = [p \in 1..N |-> y[p]]
          /\ newb = [p \in 1..N |-> IF p = P THEN FALSE ELSE b[p]]
          /\ newstate = [p \in 1..N |-> IF p = P THEN "await" ELSE state[p]]
          /\ newfailed = failed
     \/ P # 1 /\
          (\E k \in 1..N : k # P /\ (b[k] \/ x[k])) /\
          newx = [p \in 1..N |-> x[p]]
          /\ newy = [p \in 1..N |-> IF p = P THEN TRUE ELSE y[p]]
          /\ newb = [p \in 1..N |-> IF p = P THEN FALSE ELSE b[p]]
          /\ newstate = [p \in 1..N |-> IF p = P THEN "await" ELSE state[p]]
          /\ newfailed = failed)
    \/ \E P \in 1..N : 
       (/\ state[P] = "await"
        /\ (\A k \in 1..N: k # P => ~(b[k] \/ x[k]))
        /\ \/ P = 1 /\
             (x' = [p \in 1..N |-> IF p = P THEN FALSE ELSE x[p]]
              /\ b' = [p \in 1..N |-> IF p = P THEN TRUE ELSE b[p]])
           \/ P # 1 /\
              (y' = [p \in 1..N |-> IF p = P THEN FALSE ELSE y[p]]
               /\ b' = [p \in 1..N |-> IF p = P THEN TRUE ELSE b[p]]))
    \/ \E P \in 1..N : 
       (/\ state[P] = "await"
        /\ (\A k \in 1..N: ~(b[k] \/ x[k]))
        /\ \/ P = 1 /\
             (x' = [p \in 1..N |-> IF p = P THEN FALSE ELSE x[p]]
              /\ b' = [p \in 1..N |-> IF p = P THEN TRUE ELSE b[p]])
           \/ P # 1 /\
              (y' = [p \in 1..N |-> IF p = P THEN FALSE ELSE y[p]]
               /\ b' = [p \in 1..N |-> IF p = P THEN TRUE ELSE b[p]]))

Spec == Init /\ [][Next]_<<x, y, b, state, failed>>

MutualExclusion == 
    \A p, q \in 1..N: p # q => ~((b[p] \/ x[p]) /\ (b[q] \/ x[q]))

Liveness ==
    <>[](\E p \in 1..N: (b[p] \/ x[p]))

WF == WF_<<x, y, b, state, failed>>(Next)

=============================================================================