--------------------------- MODULE DijkstraMutex ---------------------------
EXTENDS Integers

CONSTANT Proc
CONSTANT defaultInitValue

(***************************************************************************
--algorithm Mutex
{ variables b = [i \in Proc |-> TRUE],
            c = [i \in Proc |-> TRUE],
            k \in Proc;
  fair process (P \in Proc)
    variable temp;
    { Li0: while (TRUE)
            {      b[self] := FALSE;
              Li1: if (k # self) { Li2:  c[self] := TRUE;
                                   Li3a: temp := k;
                                   Li3b: if (b[temp]) { Li3c: k := self };
                                   Li3d: goto Li1
                                 };
              Li4a: c[self] := FALSE;
                    temp := Proc \ {self};
              Li4b: while (temp # {})
                     { with (j \in temp)
                         { temp := temp \ {j};
                           if (~c[j]) { goto Li1 }
                         }
                     };
              cs:  skip;
              Li5: c[self] := TRUE;
              Li6: b[self] := TRUE;
              ncs: skip
            }
    }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == Proc

Init == /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        /\ temp = [self \in Proc |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "Li2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Li4a"]
             /\ UNCHANGED << b, c, k, temp >>

Li2(self) == /\ pc[self] = "Li2"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li3a"]
             /\ UNCHANGED << b, k, temp >>

Li3a(self) == /\ pc[self] = "Li3a"
              /\ temp' = [temp EXCEPT ![self] = k]
              /\ pc' = [pc EXCEPT ![self] = "Li3b"]
              /\ UNCHANGED << b, c, k >>

Li3b(self) == /\ pc[self] = "Li3b"
              /\ IF b[temp[self]]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Li3c"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, k, temp >>

Li3c(self) == /\ pc[self] = "Li3c"
              /\ k' = self
              /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, temp >>

Li3d(self) == /\ pc[self] = "Li3d"
              /\ pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li4a(self) == /\ pc[self] = "Li4a"
              /\ c' = [c EXCEPT ![self] = FALSE]
              /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
              /\ pc' = [pc EXCEPT ![self] = "Li4b"]
              /\ UNCHANGED << b, k >>

Li4b(self) == /\ pc[self] = "Li4b"
              /\ IF temp[self] # {}
                    THEN /\ \E j \in temp[self]:
                              /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                              /\ IF ~c[j]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Li1"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "Li4b"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ temp' = temp
              /\ UNCHANGED << b, c, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Li5"]
            /\ UNCHANGED << b, c, k, temp >>

Li5(self) == /\ pc[self] = "Li5"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li6"]
             /\ UNCHANGED << b, k, temp >>

Li6(self) == /\ pc[self] = "Li6"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << c, k, temp >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Li0"]
             /\ UNCHANGED << b, c, k, temp >>

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
              \/ Li3c(self) \/ Li3d(self) \/ Li4a(self) \/ Li4b(self)
              \/ cs(self) \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == (\E self \in Proc: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(P(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc

MutualExclusion == \A i, j \in Proc :
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"

Trying(i) == pc[i] \in {"Li1", "Li2", "Li3a", "Li3b", "Li3c", "Li3d", "Li4a", "Li4b"}

DeadlockFree == (\E i \in Proc : Trying(i)) ~> (\E i \in Proc : pc[i] = "cs")

StarvationFree == \A i \in Proc : Trying(i) ~> (pc[i] = "cs")

-----------------------------------------------------------------------------

(* Alternative liveness spec: processes need not leave the noncritical section. *)
LSpec == /\ Init /\ [][Next]_vars
         /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

DeadlockFreedom ==
    (\E i \in Proc : pc[i] \notin {"Li5", "Li6", "ncs"})
        ~> (\E i \in Proc : pc[i] = "cs")

=============================================================================