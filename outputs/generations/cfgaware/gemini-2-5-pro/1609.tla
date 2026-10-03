---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen, MaxValue
ASSUME ArrayLen \in 1..100 /\ MaxValue \in 1..100

(*--algorithm Quicksort
constants ArrayLen = ArrayLen, MaxValue = MaxValue;

variables arr \in [1..ArrayLen -> 1..MaxValue],
          arr_initial = arr;

procedure QS(lo, hi)
variable partition_point;
begin
  P:
    if lo < hi then
      with new_arr \in [1..ArrayLen -> 1..MaxValue],
           p \in (lo-1)..hi do
        assert /\ IsSubArrayPermutation(new_arr, arr, lo, hi)
               /\ IsPartitioned(new_arr, lo, hi, p);
        arr := new_arr;
        partition_point := p;
      end with;
      C1: call QS(lo, partition_point);
      C2: call QS(partition_point + 1, hi);
    end if;
  R: return;
end procedure;

begin (* main *)
  L:
    call QS(1, ArrayLen);
  Done:
    assert IsSorted(arr);
    assert IsPermutation(arr, arr_initial);
    while TRUE do skip end;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES arr, arr_initial, pc, stack, lo, hi, partition_point

vars == << arr, arr_initial, pc, stack, lo, hi, partition_point >>

Bag(s) == [x \in {s[i] : i \in DOMAIN s} |-> Cardinality({i \in DOMAIN s : s[i] = x})]

IsPermutation(s1, s2) == Bag(s1) = Bag(s2)

IsSorted(s) == \A i \in 1..(Len(s)-1) : s[i] <= s[i+1]

IsSubArrayPermutation(a1, a2, l, h) ==
    /\ Bag(SubSeq(a1, l, h)) = Bag(SubSeq(a2, l, h))
    /\ \A i \in (1..(l-1)) \cup ((h+1)..ArrayLen) : a1[i] = a2[i]

IsPartitioned(a, l, h, p) ==
    \A i \in l..p, j \in (p+1)..h : a[i] <= a[j]

Init == (* Global variables *)
        /\ arr \in [1..ArrayLen -> 1..MaxValue]
        /\ arr_initial = arr
        (* Main body *)
        /\ pc = "L"
        /\ stack = << >>
        /\ lo = 0
        /\ hi = 0
        /\ partition_point = 0

P == /\ pc = "P"
     /\ IF lo < hi
           THEN /\ \E new_arr \in [1..ArrayLen -> 1..MaxValue], p \in (lo-1)..hi:
                     /\ IsSubArrayPermutation(new_arr, arr, lo, hi)
                     /\ IsPartitioned(new_arr, lo, hi, p)
                     /\ arr' = new_arr
                     /\ partition_point' = p
                /\ pc' = "C1"
           ELSE /\ pc' = "R"
                /\ UNCHANGED << arr, partition_point >>
     /\ UNCHANGED << arr_initial, stack, lo, hi >>

C1 == /\ pc = "C1"
      /\ stack' = << [ procedure |-> "QS",
                       pc |-> "C2",
                       lo |-> lo,
                       hi |-> hi,
                       partition_point |-> partition_point ] >> \o stack
      /\ hi' = partition_point
      /\ pc' = "P"
      /\ UNCHANGED << arr, arr_initial, lo, partition_point >>

C2 == /\ pc = "C2"
      /\ stack' = << [ procedure |-> "QS",
                       pc |-> "R",
                       lo |-> lo,
                       hi |-> hi,
                       partition_point |-> partition_point ] >> \o stack
      /\ lo' = partition_point + 1
      /\ pc' = "P"
      /\ UNCHANGED << arr, arr_initial, hi, partition_point >>

R == /\ pc = "R"
     /\ stack # << >>
     /\ LET frame == Head(stack)
        IN /\ pc' = frame.pc
           /\ lo' = frame.lo
           /\ hi' = frame.hi
           /\ partition_point' = frame.partition_point
           /\ stack' = Tail(stack)
     /\ UNCHANGED << arr, arr_initial >>

QS == P \/ C1 \/ C2 \/ R

L == /\ pc = "L"
     /\ stack' = << [ procedure |-> "main",
                      pc |-> "Done",
                      lo |-> lo,
                      hi |-> hi,
                      partition_point |-> partition_point ] >> \o stack
     /\ lo' = 1
     /\ hi' = ArrayLen
     /\ pc' = "P"
     /\ UNCHANGED << arr, arr_initial, partition_point >>

Done == /\ pc = "Done"
        /\ Assert(IsSorted(arr), "Assertion failure at Done: IsSorted")
        /\ Assert(IsPermutation(arr, arr_initial), "Assertion failure at Done: IsPermutation")
        /\ pc' = "Done"
        /\ UNCHANGED << arr, arr_initial, stack, lo, hi, partition_point >>

Next == QS \/ L \/ Done

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================