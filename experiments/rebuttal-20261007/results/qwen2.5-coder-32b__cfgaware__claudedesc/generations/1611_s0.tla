```tla
------------------------------- MODULE MergeSortSpec -------------------------------

CONSTANTS ArrayLen

VARIABLES a, b, stack, pc, i, j, k, m, N

(*--algorithm merge_sort
variables a = [1..N -> ?], b = [1..N -> ?], stack = <<>>, pc = "Init", i = 0, j = 0, k = 0, m = 0;

procedure mergesort(l, r)
    variable mid;
begin
    if l < r then
        mid := (l + r) \div 2;
        push(stack, <<l, mid>>);
        push(stack, <<mid+1, r>>);
    else
        pc := "Merge";
    end if;
end procedure;

next == 
    case pc = "Init" ->
        /\ N \in 0..ArrayLen
        /\ a \in [1..N -> 1..N]
        /\ b \in [1..N -> 1..N]
        /\ stack = <<>>
        /\ i = 0
        /\ j = 0
        /\ k = 0
        /\ m = 0
        /\ pc' = "Start"
    [] pc = "Start" ->
        \/ /\ stack # <<>>
           /\ LET top == Head(stack)
              l == top[1]
              r == top[2]
            IN /\ i' = l
               /\ j' = r
               /\ k' = l
               /\ m' = (l + r) \div 2
               /\ pc' = "Sort"
        \/ /\ stack = <<>>
           /\ pc' = "Done"
    [] pc = "Sort" ->
        \/ /\ i' <= m
           /\ b[i']' = a[i']
           /\ i'' = i' + 1
           /\ pc' = "Sort"
        \/ /\ j' > m
           /\ b[j']' = a[j']
           /\ j'' = j' - 1
           /\ pc' = "Sort"
        \/ /\ i' > m
           /\ j' <= m
           /\ b[j']' = a[j']
           /\ j'' = j' - 1
           /\ pc' = "Sort"
        \/ /\ i' <= m
           /\ j' > m
           /\ b[i']' = a[i']
           /\ i'' = i' + 1
           /\ pc' = "Sort"
        \/ /\ i' > m
           /\ j' > m
           /\ pc' = "Merge"
    [] pc = "Merge" ->
        \/ /\ k' <= j'
           /\ b[k'] <= b[j']
           /\ a[k']' = b[k']
           /\ k'' = k' + 1
           /\ i'' = i' + 1
           /\ pc' = "Merge"
        \/ /\ k' <= j'
           /\ b[i'] < b[j']
           /\ a[k']' = b[j']
           /\ k'' = k' + 1
           /\ j'' = j' - 1
           /\ pc' = "Merge"
        \/ /\ k' > j'
           /\ pc' = "Pop"
    [] pc = "Pop" ->
        \/ /\ stack # <<>>
           /\ LET top == Head(stack)
              l == top[1]
              r == top[2]
            IN /\ stack' = Tail(stack)
               /\ i' = l
               /\ j' = r
               /\ k' = l
               /\ m' = (l + r) \div 2
               /\ pc' = "Sort"
        \/ /\ stack = <<>>
           /\ pc' = "Done"
    [] pc = "Done" ->
        /\ pc' = "Done"
end next;

Spec == 
    /\ Init
    /\ [][next]_<<a, b, stack, pc, i, j, k, m>>
    /\ WF_next(<<a, b, stack, pc, i, j, k, m>>)

Init == 
    /\ N \in 0..ArrayLen
    /\ a \in [1..N -> 1..N]
    /\ b \in [1..N -> 1..N]
    /\ stack = <<>>
    /\ pc = "Init"
    /\ i = 0
    /\ j = 0
    /\ k = 0
    /\ m = 0

Invariant == 
    \/ pc # "Done"
    \/ \A x, y \in DOMAIN a : x <= y => a[x] <= a[y]

Termination ==
    <>[](pc = "Done")

defaultInitValue(x) == CASE x = N -> 0
                         [] x = a -> [1..ArrayLen -> 0]
                         [] x = b -> [1..ArrayLen -> 0]
                         [] x = stack -> <<>>
                         [] x = pc -> "Init"
                         [] x = i -> 0
                         [] x = j -> 0
                         [] x = k -> 0
                         [] x = m -> 0
                         ELSE 0

push(seq, elem) == seq \o <<elem>>

Head(seq) == seq[1]

Tail(seq) == <<seq[i] : i \in 2..Len(seq)>> 

END MODULE
```