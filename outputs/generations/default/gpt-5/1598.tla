------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

(* --algorithmically, we consider processes 1..N -- *)
Proc == 1..N
Null == 0

VARIABLES x, y, b, S, pc

vars == << x, y, b, S, pc >>

Init ==
  /\ x = Null
  /\ y = Null
  /\ b = [i \in Proc |-> FALSE]
  /\ S = [i \in Proc |-> {}]
  /\ pc = [i \in Proc |-> "a0"]

A0_set_b(i) ==
  /\ i \in Proc
  /\ pc[i] = "a0"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "a0b"]
  /\ UNCHANGED << x, y, S >>

A0_set_x(i) ==
  /\ i \in Proc
  /\ pc[i] = "a0b"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << y, b, S >>

A1_if_y_busy(i) ==
  /\ i \in Proc
  /\ pc[i] = "a1"
  /\ y # Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "a1a"]
  /\ UNCHANGED << x, y, S >>

A1_await_y_zero(i) ==
  /\ i \in Proc
  /\ pc[i] = "a1a"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "a0"]
  /\ UNCHANGED << x, y, b, S >>

A1_to_A2(i) ==
  /\ i \in Proc
  /\ pc[i] = "a1"
  /\ y = Null
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "a2"]
  /\ UNCHANGED << x, b, S >>

A2_if_x_me(i) ==
  /\ i \in Proc
  /\ pc[i] = "a2"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

A2_if_x_not_me(i) ==
  /\ i \in Proc
  /\ pc[i] = "a2"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ S' = [S EXCEPT ![i] = Proc \ {i}]
  /\ pc' = [pc EXCEPT ![i] = "a3a"]
  /\ UNCHANGED << x, y >>

A3a_progress(i) ==
  /\ i \in Proc
  /\ pc[i] = "a3a"
  /\ S[i] # {}
  /\ \E k \in S[i]: ~ b[k]
  /\ LET j == CHOOSE k \in S[i]: ~ b[k]
     IN /\ S' = [S EXCEPT ![i] = S[i] \ {j}]
        /\ pc' = [pc EXCEPT ![i] = "a3a"]
        /\ UNCHANGED << x, y, b >>

A3a_done(i) ==
  /\ i \in Proc
  /\ pc[i] = "a3a"
  /\ S[i] = {}
  /\ pc' = [pc EXCEPT ![i] = "a3c"]
  /\ UNCHANGED << x, y, b, S >>

A3c_if_y_me(i) ==
  /\ i \in Proc
  /\ pc[i] = "a3c"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

A3c_if_y_not_me(i) ==
  /\ i \in Proc
  /\ pc[i] = "a3c"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "a3d"]
  /\ UNCHANGED << x, y, b, S >>

A3d_await_y_zero(i) ==
  /\ i \in Proc
  /\ pc[i] = "a3d"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "a0"]
  /\ UNCHANGED << x, y, b, S >>

Cs_to_exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b, S >>

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ y' = Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "a0"]
  /\ UNCHANGED << x, S >>

ProcStep(i) ==
   A0_set_b(i)
\/ A0_set_x(i)
\/ A1_if_y_busy(i)
\/ A1_await_y_zero(i)
\/ A1_to_A2(i)
\/ A2_if_x_me(i)
\/ A2_if_x_not_me(i)
\/ A3a_progress(i)
\/ A3a_done(i)
\/ A3c_if_y_me(i)
\/ A3c_if_y_not_me(i)
\/ A3d_await_y_zero(i)
\/ Cs_to_exit(i)
\/ Exit(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

MutualExclusion ==
  \A p \in Proc : \A q \in Proc : p # q => ~ (pc[p] = "cs" /\ pc[q] = "cs")

Liveness ==
  []<>(\E i \in Proc : pc[i] = "cs")

=============================================================================