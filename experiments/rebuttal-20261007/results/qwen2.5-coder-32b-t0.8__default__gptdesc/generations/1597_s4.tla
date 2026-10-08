---- MODULE LamportFastMutex ----

EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES x, y, b, state, failed

Init == /\ x = 1 
        /\ y = 1 
        /\ \A p \in 1..N : b[p] = FALSE
        /\ \A p \in 1..N : state[p] = "idle"
        /\ \A p \in 1..N : failed[p] = FALSE

Next == \/ /\ state[1] = "idle"
             /\ ~failed[1]
             /\ x # y
             /\ y # 1
             /\ b[y] = FALSE
             /\ LET new_x == CHOOSE z \in {2 .. N} \ {y, x} : TRUE
                IN \/ /\ new_x = 2
                       /\ x' = 2
                       /\ state'[1] = "awaiting"
                   \/ /\ new_x = y
                      /\ y' = 2
                      /\ state'[1] = "awaiting"
             []
           \/ /\ state[1] = "awaiting"
              /\ ~failed[1]
              /\ b[x] = FALSE
              /\ LET new_y == CHOOSE z \in {3 .. N} \ {x, y} : TRUE
                 IN \/ /\ new_y = 3
                        /\ y' = 3
                        /\ state'[1] = "requesting"
                    \/ /\ new_y = x
                       /\ b[y]' = TRUE
                       /\ state'[1] = "waiting"
           []
           \/ /\ state[1] = "requesting"
              /\ ~failed[1]
              /\ \A q \in 2..N : q # y => b[q] = FALSE
              /\ state'[1] = "holding"
           []
           \/ /\ state[1] = "holding"
              /\ ~failed[1]
              /\ state'[1] = "idle"
              /\ x' = y
              /\ b[y]' = FALSE
           []
           \/ \E p \in 2..N : 
                (/\ state[p] = "idle"
                  /\ ~failed[p]
                  /\ LET new_x == CHOOSE z \in {1 .. N} \ {x, y} : TRUE
                     IN \/ /\ new_x = 1
                            /\ x' = 1
                            /\ state'[p] = "awaiting"
                        \/ /\ new_x = y
                           /\ y' = 1
                           /\ state'[p] = "awaiting")
           []
           \/ \E p \in 2..N : 
                (/\ state[p] = "awaiting"
                  /\ ~failed[p]
                  /\ b[x] = FALSE
                  /\ LET new_y == CHOOSE z \in {1, 3 .. N} \ {x, y} : TRUE
                     IN \/ /\ new_y = 1
                            /\ y' = 1
                            /\ state'[p] = "requesting"
                        \/ /\ new_y = x
                           /\ b[y]' = TRUE
                           /\ state'[p] = "waiting")
           []
           \/ \E p \in 2..N : 
                (/\ state[p] = "requesting"
                  /\ ~failed[p]
                  /\ \A q \in {1} \cup {3 .. N} \ {y} : q # y => b[q] = FALSE
                  /\ state'[p] = "holding")
           []
           \/ \E p \in 2..N : 
                (/\ state[p] = "holding"
                  /\ ~failed[p]
                  /\ state'[p] = "idle"
                  /\ x' = y
                  /\ b[y]' = FALSE)
           []
           \/ \E p \in 1..N : failed'[p] = TRUE

MutualExclusion == \A p, q \in 1..N : <<p, q>> \notin IDENTITY => ~ (state[p] = "holding" /\ state[q] = "holding")

Liveness == [](<>[] (\E p \in 1..N : state[p] = "holding"))

Spec == Init /\ [][Next]_<<x, y, b, state, failed>> /\ MutualExclusion /\ Liveness

WF_spec == WF_(Next, <<x, y, b, state, failed>>)

====