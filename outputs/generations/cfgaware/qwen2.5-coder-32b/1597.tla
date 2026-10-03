------------------------------- MODULE FastMutualExclusion -------------------------------
VARIABLES x, y, b, state

CONSTANTS N

(*--algorithm fast_mutual_exclusion
variables x = 1, y = 1, b = [i \in 2..N -> FALSE];

process P1 = 
{ while (TRUE)
    { await (\A i \in 2..N: ~b[i]);
      x := 0;
      await (y = 1);
      y := 0;
      /\* Critical Section *\
      y := 1;
      x := 1;
    }
}

process P2 \in 2..N =
{ while (TRUE)
    { b[self] := TRUE;
      await (x = 1);
      y := self;
      await (\A i \in 2..N \ {self}: ~b[i]);
      b[self] := FALSE;
      /\* Critical Section *\
      y := 1;
    }
}
end algorithm *)

Spec ==
  Init /\ [][Next]_<<x, y, b>> /\ WF_pc

Init == 
  /\ x = 1
  /\ y = 1
  /\ b \in [2..N -> BOOLEAN]
  /\ (\A i \in 2..N: b[i] = FALSE)

Next ==
  \/ /\ pc[1] = "await (\A i \in 2..N: ~b[i]);"
     /\ (\A i \in 2..N: ~b[i])
     /\ x' = 0
     /\ y' = y
     /\ b' = b
     /\ pc'[1] = "x := 0;"
  \/ /\ pc[1] = "x := 0;"
     /\ x = 0
     /\ await (y = 1)
     /\ y' = 0
     /\ x' = x
     /\ b' = b
     /\ pc'[1] = "await (y = 1);"
  \/ /\ pc[1] = "await (y = 1);"
     /\ y = 0
     /\ x' = x
     /\ y' = 0
     /\ b' = b
     /\ pc'[1] = "y := 0;"
  \/ /\ pc[1] = "y := 0;"
     /\ y = 0
     /\ x' = 1
     /\ y' = 1
     /\ b' = b
     /\ pc'[1] = "y := 1;"
  \/ /\ pc[1] = "y := 1;"
     /\ y = 1
     /\ x' = 1
     /\ y' = 1
     /\ b' = b
     /\ pc'[1] = "await (\A i \in 2..N: ~b[i]);"
  \/ \E j \in 2..N:
       /\ pc[j] = "b[self] := TRUE;"
       /\ b' = [b EXCEPT ![j] = TRUE]
       /\ x' = x
       /\ y' = y
       /\ pc'[j] = "await (x = 1);"
  \/ \E j \in 2..N:
       /\ pc[j] = "await (x = 1);"
       /\ x = 1
       /\ b' = b
       /\ y' = j
       /\ pc'[j] = "y := self;"
  \/ \E j \in 2..N:
       /\ pc[j] = "y := self;"
       /\ await (\A i \in 2..N \ {j}: ~b[i])
       /\ b' = [b EXCEPT ![j] = FALSE]
       /\ x' = x
       /\ y' = y
       /\ pc'[j] = "await (\A i \in 2..N \ {self}: ~b[i]);"
  \/ \E j \in 2..N:
       /\ pc[j] = "await (\A i \in 2..N \ {j}: ~b[i]);"
       /\ (\A i \in 2..N \ {j}: ~b[i])
       /\ b' = b
       /\ x' = x
       /\ y' = 1
       /\ pc'[j] = "y := 1;"

WF_pc == 
  WF_vars(<<pc[1], pc[2..N]>>, <<P1, P2>>)

Invariant ==
  \/ y = 1
  \/ \E i \in 2..N: y = i

Liveness ==
  <>[] (\E i \in 1..N: pc[i] = "y := 1;")

=============================================================================