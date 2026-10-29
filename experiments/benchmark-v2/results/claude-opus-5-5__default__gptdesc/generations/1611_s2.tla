------------------------------ MODULE Mergesort ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N, ArrayLen

ASSUME /\ N \in Nat \ {0}
       /\ ArrayLen \in Nat

(***************************************************************************
--algorithm Mergesort
variables a \in UNION {[1..len -> 1..N] : len \in 0..ArrayLen},
          b = a;

procedure mergesort(lo = 1, hi = 0)
  variables mid = 0, i = 0, j = 0, k = 0;
begin
ms1: if lo < hi then
       mid := (lo + hi) \div 2;
ms2:   call mergesort(lo, mid);
ms3:   call mergesort(mid + 1, hi);
ms4:   i := lo; j := mid + 1; k := lo;
ms5:   while k <= hi do
         if j > hi \/ (i <= mid /\ a[i] <= a[j]) then
           b[k] := a[i]; i := i + 1
         else
           b[k] := a[j]; j := j + 1
         end if;
         k := k + 1
       end while;
ms6:   a := [x \in DOMAIN a |-> IF x \in lo..hi THEN b[x] ELSE a[x]];
     end if;
ms7: return;
end procedure;

begin
main: call mergesort(1, Len(a));
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES a, b, pc, stack, lo, hi, mid, i, j, k

vars == << a, b, pc, stack, lo, hi, mid, i, j, k >>

Arrays == UNION {[1..len -> 1..N] : len \in 0..ArrayLen}

Init == /\ a \in Arrays
        /\ b = a
        /\ stack = << >>
        /\ lo = 1
        /\ hi = 0
        /\ mid = 0
        /\ i = 0
        /\ j = 0
        /\ k = 0
        /\ pc = "main"

ms1 == /\ pc = "ms1"
       /\ IF lo < hi
            THEN /\ mid' = (lo + hi) \div 2
                 /\ pc' = "ms2"
            ELSE /\ pc' = "ms7"
                 /\ mid' = mid
       /\ UNCHANGED << a, b, stack, lo, hi, i, j, k >>

ms2 == /\ pc = "ms2"
       /\ stack' = << [ procedure |-> "mergesort",
                        pc        |-> "ms3",
                        lo        |-> lo,
                        hi        |-> hi,
                        mid       |-> mid,
                        i         |-> i,
                        j         |-> j,
                        k         |-> k ] >> \o stack
       /\ lo' = lo
       /\ hi' = mid
       /\ mid' = 0
       /\ i' = 0
       /\ j' = 0
       /\ k' = 0
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms3 == /\ pc = "ms3"
       /\ stack' = << [ procedure |-> "mergesort",
                        pc        |-> "ms4",
                        lo        |-> lo,
                        hi        |-> hi,
                        mid       |-> mid,
                        i         |-> i,
                        j         |-> j,
                        k         |-> k ] >> \o stack
       /\ lo' = mid + 1
       /\ hi' = hi
       /\ mid' = 0
       /\ i' = 0
       /\ j' = 0
       /\ k' = 0
       /\ pc' = "ms1"
       /\ UNCHANGED << a, b >>

ms4 == /\ pc = "ms4"
       /\ i' = lo
       /\ j' = mid + 1
       /\ k' = lo
       /\ pc' = "ms5"
       /\ UNCHANGED << a, b, stack, lo, hi, mid >>

ms5 == /\ pc = "ms5"
       /\ IF k <= hi
            THEN /\ IF j > hi \/ (i <= mid /\ a[i] <= a[j])
                      THEN /\ b' = [b EXCEPT ![k] = a[i]]
                           /\ i' = i + 1
                           /\ j' = j
                      ELSE /\ b' = [b EXCEPT ![k] = a[j]]
                           /\ j' = j + 1
                           /\ i' = i
                 /\ k' = k + 1
                 /\ pc' = "ms5"
            ELSE /\ pc' = "ms6"
                 /\ UNCHANGED << b, i, j, k >>
       /\ UNCHANGED << a, stack, lo, hi, mid >>

ms6 == /\ pc = "ms6"
       /\ a' = [x \in DOMAIN a |-> IF x \in lo..hi THEN b[x] ELSE a[x]]
       /\ pc' = "ms7"
       /\ UNCHANGED << b, stack, lo, hi, mid, i, j, k >>

ms7 == /\ pc = "ms7"
       /\ pc' = Head(stack).pc
       /\ lo' = Head(stack).lo
       /\ hi' = Head(stack).hi
       /\ mid' = Head(stack).mid
       /\ i' = Head(stack).i
       /\ j' = Head(stack).j
       /\ k' = Head(stack).k
       /\ stack' = Tail(stack)
       /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms2 \/ ms3 \/ ms4 \/ ms5 \/ ms6 \/ ms7

main == /\ pc = "main"
        /\ stack' = << [ procedure |-> "mergesort",
                         pc        |-> "Done",
                         lo        |-> lo,
                         hi        |-> hi,
                         mid       |-> mid,
                         i         |-> i,
                         j         |-> j,
                         k         |-> k ] >> \o stack
        /\ lo' = 1
        /\ hi' = Len(a)
        /\ mid' = 0
        /\ i' = 0
        /\ j' = 0
        /\ k' = 0
        /\ pc' = "ms1"
        /\ UNCHANGED << a, b >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == main \/ mergesort \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Properties *)

TypeOK == /\ a \in Arrays
          /\ DOMAIN b = DOMAIN a
          /\ pc \in {"main", "ms1", "ms2", "ms3", "ms4", "ms5", "ms6", "ms7", "Done"}
          /\ lo \in Int /\ hi \in Int /\ mid \in Int
          /\ i \in Int /\ j \in Int /\ k \in Int

IsSorted(s) == \A x, y \in DOMAIN s : x < y => s[x] <= s[y]

Sorted == (pc = "Done") => IsSorted(a)

=============================================================================