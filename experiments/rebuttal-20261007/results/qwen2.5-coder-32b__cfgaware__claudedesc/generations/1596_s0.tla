------------------------------- MODULE FastMutex2 -------------------------------

CONSTANTS N, M

VARIABLES x, y, b, loop1, loop2, fail1, fail2

(*--algorithm fast_mutex
variables 
  x = 0,
  y = 0,
  b = [i \in 1..N -> FALSE],
  loop1 = 0,
  loop2 = 0,
  fail1 = FALSE,
  fail2 = FALSE;

process (Proc1 \in 1..M)
begin
Loop1:
  while TRUE do
    b[Proc1] := TRUE;
    x := Proc1;
    if y # 0 then
      b[Proc1] := FALSE;
      await y = 0;
    else
      y := Proc1;
      if x # Proc1 then
        b[Proc1] := FALSE;
        await \A j \in 1..N: b[j] = FALSE;
        if y # Proc1 then
          fail1 := TRUE;
        end if;
        await y = 0;
      else
        fail1 := FALSE;
        critical_section1:
        y := 0;
        b[Proc1] := FALSE;
        loop1 := loop1 + 1;
      end if;
    end if;
end while;

process (Proc2 \in M+1..N)
begin
Loop2:
  while TRUE do
    b[Proc2] := TRUE;
    x := Proc2;
    if y # 0 then
      b[Proc2] := FALSE;
      await y = 0;
    else
      y := Proc2;
      if x # Proc2 then
        b[Proc2] := FALSE;
        await \A j \in 1..N: b[j] = FALSE;
        if y # Proc2 then
          fail2 := TRUE;
        end if;
        await y = 0;
      else
        fail2 := FALSE;
        critical_section2:
        y := 0;
        b[Proc2] := FALSE;
        loop2 := loop2 + 1;
      end if;
    end if;
end while;

end algorithm *)

Spec ==
  /\ Init
  /\ \A i \in 1..N: [][Next_i(i)]_<<x, y, b, loop1, loop2, fail1, fail2>>
  /\ WF_\{i \in 1..N : ProcAction_i(i)}(<<x, y, b, loop1, loop2, fail1, fail2>>)

Init ==
  /\ x = 0
  /\ y = 0
  /\ \A i \in 1..N: b[i] = FALSE
  /\ loop1 = 0
  /\ loop2 = 0
  /\ fail1 = FALSE
  /\ fail2 = FALSE

Next_i(i) ==
  \/ ProcAction_i(i)

ProcAction_1 ==
  \/ /\ b[1] = FALSE
     /\ x' = 1
     /\ y' \in {y, 1}
     /\ b' = [b EXCEPT ![1] = TRUE]
     /\ loop1' = loop1
     /\ loop2' = loop2
     /\ fail1' = fail1
     /\ fail2' = fail2
  \/ /\ b[1] = TRUE
     /\ x \in {0, 1}
     /\ y # 0
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ loop1' = loop1
     /\ loop2' = loop2
     /\ fail1' = fail1
     /\ fail2' = fail2
  \/ /\ b[1] = TRUE
     /\ x \in {0, 1}
     /\ y = 0
     /\ x' \in {x, 1}
     /\ y' \in {y, 1}
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ loop1' = loop1
     /\ loop2' = loop2
     /\ fail1' = fail1
     /\ fail2' = fail2
  \/ /\ b[1] = TRUE
     /\ x = 1
     /\ y = 1
     /\ \A j \in 1..N: b[j] = FALSE
     /\ x' \in {x, 0}
     /\ y' \in {y, 0}
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ loop1' = IF x' = 0 THEN loop1 + 1 ELSE loop1 ENDIF
     /\ loop2' = loop2
     /\ fail1' = IF x' = 0 THEN FALSE ELSE fail1 ENDIF
     /\ fail2' = fail2

ProcAction_2 ==
  \/ /\ b[2] = FALSE
     /\ x' = 2
     /\ y' \in {y, 2}
     /\ b' = [b EXCEPT ![2] = TRUE]
     /\ loop1' = loop1
     /\ loop2' = loop2
     /\ fail1' = fail1
     /\ fail2' = fail2
  \/ /\ b[2] = TRUE
     /\ x \in {0, 2}
     /\ y # 0
     /\ b' = [b EXCEPT ![2] = FALSE]
     /\ loop1' = loop1
     /\ loop2' = loop2
     /\ fail1' = fail1
     /\ fail2' = fail2
  \/ /\ b[2] = TRUE
     /\ x \in {0, 2}
     /\ y = 0
     /\ x' \in {x, 2}
     /\ y' \in {y, 2}
     /\ b' = [b EXCEPT ![2] = FALSE]
     /\ loop1' = loop1
     /\ loop2' = loop2
     /\ fail1' = fail1
     /\ fail2' = fail2
  \/ /\ b[2] = TRUE
     /\ x = 2
     /\ y = 2
     /\ \A j \in 1..N: b[j] = FALSE
     /\ x' \in {x, 0}
     /\ y' \in {y, 0}
     /\ b' = [b EXCEPT ![2] = FALSE]
     /\ loop1' = loop1
     /\ loop2' = IF x' = 0 THEN loop2 + 1 ELSE loop2 ENDIF
     /\ fail1' = fail1
     /\ fail2' = IF x' = 0 THEN FALSE ELSE fail2 ENDIF

Invariant ==
  \A i, j \in 1..N: i # j => \/ b[i] = FALSE \/ b[j] = FALSE \/ (y # i) \/ (y # j)

Liveness ==
  <>[] (\E i \in 1..N: /\ b[i] = FALSE /\ y = i /\ fail_i = FALSE)

=============================================================================