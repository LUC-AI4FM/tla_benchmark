------------------------------ MODULE MergeSort ------------------------------
(***************************************************************************)
(* Merge sort, transcribed from Sedgewick, "Algorithms" (2nd ed.), p. 166 *)
(*                                                                         *)
(*   procedure mergesort(l, r: integer);                                   *)
(*     var i, j, k, m: integer;                                            *)
(*     begin                                                               *)
(*     if r-l > 0 then                                                     *)
(*       begin                                                             *)
(*       m := (r+l) div 2;                                                 *)
(*       mergesort(l, m); mergesort(m+1, r);                               *)
(*       for i := m downto l do b[i] := a[i];                              *)
(*       for j := m+1 to r do b[r+m+1-j] := a[j];                          *)
(*       for k := l to r do                                                *)
(*         if b[i] < b[j]                                                  *)
(*           then begin a[k] := b[i]; i := i+1 end                         *)
(*           else begin a[k] := b[j]; j := j-1 end;                        *)
(*       end                                                               *)
(*     end;                                                                *)
(*                                                                         *)
(* The recursion is modeled with an explicit call stack.                   *)
(* Validate with MaxLen = 2.                                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT MaxLen

ASSUME MaxLen \in Nat

VARIABLES a,      \* the array being sorted
          b,      \* the temporary buffer
          l, r,   \* procedure parameters
          i, j, k, m,  \* procedure locals
          pc,     \* program counter
          stack   \* call stack of saved frames

vars == << a, b, l, r, i, j, k, m, pc, stack >>

Frame(ret) == [ret |-> ret, l |-> l, r |-> r, m |-> m, i |-> i, j |-> j, k |-> k]

-----------------------------------------------------------------------------
Init ==
  \E N \in 0..MaxLen :
     /\ a \in [1..N -> 0..N]
     /\ b = [x \in 1..N |-> 0]
     /\ l = 1
     /\ r = N
     /\ i = 0 /\ j = 0 /\ k = 0 /\ m = 0
     /\ pc = "ms1"
     /\ stack = << [ret |-> "Done", l |-> 0, r |-> 0, m |-> 0,
                    i |-> 0, j |-> 0, k |-> 0] >>

\* Test r - l > 0; if so compute m and call mergesort(l, m).
MS1 ==
  /\ pc = "ms1"
  /\ IF r - l > 0
       THEN LET mid == (r + l) \div 2 IN
              /\ stack' = << [ret |-> "ms2", l |-> l, r |-> r, m |-> mid,
                              i |-> i, j |-> j, k |-> k] >> \o stack
              /\ m' = mid
              /\ r' = mid
              /\ pc' = "ms1"
              /\ UNCHANGED << a, b, l, i, j, k >>
       ELSE /\ pc' = "ret"
            /\ UNCHANGED << a, b, l, r, i, j, k, m, stack >>

\* Call mergesort(m+1, r).
MS2 ==
  /\ pc = "ms2"
  /\ stack' = << Frame("ms3") >> \o stack
  /\ l' = m + 1
  /\ pc' = "ms1"
  /\ UNCHANGED << a, b, r, i, j, k, m >>

\* Start first copy loop: i := m.
MS3 ==
  /\ pc = "ms3"
  /\ i' = m
  /\ pc' = "cp1"
  /\ UNCHANGED << a, b, l, r, j, k, m, stack >>

\* for i := m downto l do b[i] := a[i]   (leaves i = l)
CP1 ==
  /\ pc = "cp1"
  /\ IF i >= l
       THEN /\ b' = [b EXCEPT ![i] = a[i]]
            /\ i' = i - 1
            /\ UNCHANGED << j, pc >>
       ELSE /\ i' = l
            /\ j' = m + 1
            /\ pc' = "cp2"
            /\ UNCHANGED b
  /\ UNCHANGED << a, l, r, k, m, stack >>

\* for j := m+1 to r do b[r+m+1-j] := a[j]   (leaves j = r)
CP2 ==
  /\ pc = "cp2"
  /\ IF j <= r
       THEN /\ b' = [b EXCEPT ![r + m + 1 - j] = a[j]]
            /\ j' = j + 1
            /\ UNCHANGED << k, pc >>
       ELSE /\ j' = r
            /\ k' = l
            /\ pc' = "mg"
            /\ UNCHANGED b
  /\ UNCHANGED << a, l, r, i, m, stack >>

\* for k := l to r do if b[i] < b[j] then ... else ...
Merge ==
  /\ pc = "mg"
  /\ IF k <= r
       THEN /\ IF b[i] < b[j]
                 THEN /\ a' = [a EXCEPT ![k] = b[i]]
                      /\ i' = i + 1
                      /\ UNCHANGED j
                 ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                      /\ j' = j - 1
                      /\ UNCHANGED i
            /\ k' = k + 1
            /\ UNCHANGED pc
       ELSE /\ pc' = "ret"
            /\ UNCHANGED << a, i, j, k >>
  /\ UNCHANGED << b, l, r, m, stack >>

\* Return from procedure: restore caller's frame.
Return ==
  /\ pc = "ret"
  /\ LET fr == Head(stack) IN
       /\ pc' = fr.ret
       /\ l' = fr.l
       /\ r' = fr.r
       /\ m' = fr.m
       /\ i' = fr.i
       /\ j' = fr.j
       /\ k' = fr.k
  /\ stack' = Tail(stack)
  /\ UNCHANGED << a, b >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == MS1 \/ MS2 \/ MS3 \/ CP1 \/ CP2 \/ Merge \/ Return \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety: upon termination the array is sorted in non-decreasing order.
Sorted ==
  pc = "Done" =>
    \A x, y \in DOMAIN a : x < y => a[x] <= a[y]

TypeOK ==
  /\ pc \in {"ms1", "ms2", "ms3", "cp1", "cp2", "mg", "ret", "Done"}
  /\ stack \in Seq([ret : {"ms2", "ms3", "Done"},
                    l : Int, r : Int, m : Int, i : Int, j : Int, k : Int])

\* Liveness: the algorithm always eventually terminates.
Termination == <>(pc = "Done")

=============================================================================