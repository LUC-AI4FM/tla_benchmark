---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen, defaultInitValue

ASSUME ArrayLen \in Nat

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

(***************************************************************************
--algorithm MergeSort
variables a \in UNION {[1..N -> 1..N] : N \in 0..ArrayLen},
          b = [x \in DOMAIN a |-> 0];

procedure mergesort(l, r)
  variables i, j, k, m;
  begin
  ms1: if l < r then
         m := (l + r) \div 2;
  ms2:   call mergesort(l, m);
  ms3:   call mergesort(m + 1, r);
  ms3b:  i := l;
  ms4:   while i <= m do
           b[i] := a[i];
           i := i + 1
         end while;
         j := m + 1;
  ms5:   while j <= r do
           b[r + m + 1 - j] := a[j];
           j := j + 1
         end while;
         i := l; j := r; k := l;
  ms6:   while k <= r do
           if b[i] <= b[j] then
             a[k] := b[i]; i := i + 1
           else
             a[k] := b[j]; j := j - 1
           end if;
           k := k + 1
         end while
       end if;
  ms7: return
  end procedure;

begin
  main: call mergesort(1, Len(a));
end algorithm
***************************************************************************)

VARIABLES a, b, pc, stack, l, r, i, j, k, m

vars == << a, b, pc, stack, l, r, i, j, k, m >>

Init ==
    /\ a \in UNION {[1..N -> 1..N] : N \in 0..ArrayLen}
    /\ b = [x \in DOMAIN a |-> 0]
    /\ stack = << >>
    /\ l = defaultInitValue
    /\ r = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue
    /\ m = defaultInitValue
    /\ pc = "main"

Frame(retpc) ==
    [ procedure |-> "mergesort",
      pc        |-> retpc,
      i         |-> i,
      j         |-> j,
      k         |-> k,
      m         |-> m,
      l         |-> l,
      r         |-> r ]

ms1 == /\ pc = "ms1"
       /\ IF l < r
             THEN /\ m' = (l + r) \div 2
                  /\ pc' = "ms2"
             ELSE /\ pc' = "ms7"
                  /\ UNCHANGED m
       /\ UNCHANGED << a, b, stack, l, r, i, j, k >>

ms2 == /\ pc = "ms2"
       /\ l' = l
       /\ r' = m
       /\ stack' = << Frame("ms3") >> \o stack
       /\ i' = defaultInitValue
       /\ j' = defaultInitValue
       /\ k' = defaultInitValue
       /\ m' = defaultInitValue
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms3 == /\ pc = "ms3"
       /\ l' = m + 1
       /\ r' = r
       /\ stack' = << Frame("ms3b") >> \o stack
       /\ i' = defaultInitValue
       /\ j' = defaultInitValue
       /\ k' = defaultInitValue
       /\ m' = defaultInitValue
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms3b == /\ pc = "ms3b"
        /\ i' = l
        /\ pc' = "ms4"
        /\ UNCHANGED << a, b, stack, l, r, j, k, m >>

ms4 == /\ pc = "ms4"
       /\ IF i <= m
             THEN /\ b' = [b EXCEPT ![i] = a[i]]
                  /\ i' = i + 1
                  /\ pc' = "ms4"
                  /\ UNCHANGED j
             ELSE /\ j' = m + 1
                  /\ pc' = "ms5"
                  /\ UNCHANGED << b, i >>
       /\ UNCHANGED << a, stack, l, r, k, m >>

ms5 == /\ pc = "ms5"
       /\ IF j <= r
             THEN /\ b' = [b EXCEPT ![r + m + 1 - j] = a[j]]
                  /\ j' = j + 1
                  /\ pc' = "ms5"
                  /\ UNCHANGED << i, k >>
             ELSE /\ i' = l
                  /\ j' = r
                  /\ k' = l
                  /\ pc' = "ms6"
                  /\ UNCHANGED b
       /\ UNCHANGED << a, stack, l, r, m >>

ms6 == /\ pc = "ms6"
       /\ IF k <= r
             THEN /\ IF b[i] <= b[j]
                        THEN /\ a' = [a EXCEPT ![k] = b[i]]
                             /\ i' = i + 1
                             /\ UNCHANGED j
                        ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                             /\ j' = j - 1
                             /\ UNCHANGED i
                  /\ k' = k + 1
                  /\ pc' = "ms6"
             ELSE /\ pc' = "ms7"
                  /\ UNCHANGED << a, i, j, k >>
       /\ UNCHANGED << b, stack, l, r, m >>

ms7 == /\ pc = "ms7"
       /\ pc' = Head(stack).pc
       /\ i' = Head(stack).i
       /\ j' = Head(stack).j
       /\ k' = Head(stack).k
       /\ m' = Head(stack).m
       /\ l' = Head(stack).l
       /\ r' = Head(stack).r
       /\ stack' = Tail(stack)
       /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms2 \/ ms3 \/ ms3b \/ ms4 \/ ms5 \/ ms6 \/ ms7

main == /\ pc = "main"
        /\ l' = 1
        /\ r' = Len(a)
        /\ stack' = << Frame("Done") >> \o stack
        /\ i' = defaultInitValue
        /\ j' = defaultInitValue
        /\ k' = defaultInitValue
        /\ m' = defaultInitValue
        /\ pc' = "ms1"
        /\ UNCHANGED << a, b >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == mergesort \/ main \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

Invariant ==
    pc = "Done" =>
        \A x, y \in DOMAIN a : x < y => a[x] <= a[y]

\* A state in which sorting has completed.
Sorted == pc = "Done"

\* A single merge step: moving one element from b back into a.
MergeStep == ms6 /\ k <= r

\* Coverage counters: register 1 counts completed-sort states,
\* register 2 counts merge-step transitions.
_POSSIBLE ==
    /\ IF Sorted THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF MergeStep THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

PossibleCounts ==
    /\ TLCGet(1) = 12
    /\ TLCGet(2) = 8

=============================================================================