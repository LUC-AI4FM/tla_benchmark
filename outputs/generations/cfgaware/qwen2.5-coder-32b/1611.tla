------------------------------- MODULE MergeSortSpec -------------------------------

CONSTANTS ArrayLen

VARIABLES a, b, stack, pc

(*--algorithm mergesort
variables a, b, stack, pc;

begin
    Init:
        with n \in 1..ArrayLen do
            a[n] := defaultInitValue;
        endwith;
        stack := <<>>;
        pc := "Start";

    while pc # "Done" do

        if pc = "Start" then
            if ArrayLen > 0 then
                stack := <<1, ArrayLen, "Merge">>;
                pc := "Sort";
            else
                pc := "Done";
            end if;

        elsif pc = "Sort" then
            with l \in [stack[1]], r \in [stack[2]] do
                if l < r then
                    let m \in (l + r) \div 2 do
                        stack := <<l, m, "Merge">> \o stack;
                        stack := <<m+1, r, "Sort">> \o stack;
                        pc := "Sort";
                    end let;
                else
                    stack := Tail(stack);
                    pc := Head(stack)[3];
                end if;
            end with;

        elsif pc = "Merge" then
            with l \in [stack[1]], r \in [stack[2]] do
                let m \in (l + r) \div 2 do
                    i := l; j := m+1; k := l;
                    while i <= m /\ j <= r do
                        if a[i] <= a[j] then
                            b[k] := a[i];
                            i := i + 1;
                        else
                            b[k] := a[j];
                            j := j + 1;
                        end if;
                        k := k + 1;
                    end while;

                    while i <= m do
                        b[k] := a[i];
                        i := i + 1;
                        k := k + 1;
                    end while;

                    while j <= r do
                        b[k] := a[j];
                        j := j + 1;
                        k := k + 1;
                    end while;

                    with n \in l..r do
                        a[n] := b[n];
                    end with;
                end let;
                stack := Tail(stack);
                pc := Head(stack)[3];
            end with;

        else
            pc := "Done";

    end while;
end algorithm *)

\* Definitions for the TLA+ specification

defaultInitValue == 0

Spec ==
    /\ Init
    /\ [][Next]_<<a, b, stack, pc>>
    /\ WF_next(<<a, b, stack, pc>>)

Init ==
    /\ a \in [1..ArrayLen -> Nat]
    /\ b \in [1..ArrayLen -> Nat]
    /\ stack = <<>>
    /\ pc = "Start"

Next ==
    \/ pc = "Start" /\ StartAction
    \/ pc = "Sort"  /\ SortAction
    \/ pc = "Merge" /\ MergeAction

StartAction ==
    /\ ArrayLen > 0
    /\ stack' = <<1, ArrayLen, "Merge">>
    /\ pc' = "Sort"
    \/ ArrayLen = 0
    /\ stack' = stack
    /\ pc' = "Done"

SortAction ==
    \E l \in 1..ArrayLen, r \in 1..ArrayLen :
        /\ l < r
        /\ stack = <<l, r, "Merge">> \o tailStack
        /\ LET m == (l + r) \div 2 IN
            /\ stack' = <<l, m, "Merge">> \o <<m+1, r, "Sort">> \o tailStack
            /\ pc' = "Sort"
    \/ \E l \in 1..ArrayLen, r \in 1..ArrayLen :
        /\ l >= r
        /\ stack = <<l, r, action>> \o tailStack
        /\ stack' = tailStack
        /\ pc' = action

MergeAction ==
    \E l \in 1..ArrayLen, r \in 1..ArrayLen :
        /\ stack = <<l, r, action>> \o tailStack
        /\ LET m == (l + r) \div 2 IN
            /\ i \in l..m
            /\ j \in m+1..r
            /\ k \in l..r
            /\ MergeStep(l, m, r, i, j, k)
            /\ stack' = tailStack
            /\ pc' = action

MergeStep(l, m, r, i, j, k) ==
    \/ i <= m /\ j <= r /\
        (/\ a[i] <= a[j]
         /\ b[k]' = a[i]
         /\ i' = i + 1
         /\ j' = j
         /\ k' = k + 1)
        \/
        (/\ a[i] > a[j]
         /\ b[k]' = a[j]
         /\ i' = i
         /\ j' = j + 1
         /\ k' = k + 1)
    \/ i <= m /\
        (/\ b[k]' = a[i]
         /\ i' = i + 1
         /\ j' = j
         /\ k' = k + 1)
    \/ j <= r /\
        (/\ b[k]' = a[j]
         /\ i' = i
         /\ j' = j + 1
         /\ k' = k + 1)
    \/ /\ i > m
       /\ j > r
       /\ \A n \in l..r : a[n]' = b[n]

WF_next(vars) ==
    WF_vars(Next, vars)

Termination ==
    <>(pc = "Done")

Invariant ==
    /\ pc \in {"Start", "Sort", "Merge", "Done"}
    /\ stack \in SUBSET [1..3 -> {"Sort", "Merge"}]
    /\ a \in [1..ArrayLen -> Nat]
    /\ b \in [1..ArrayLen -> Nat]

Sorted(subarray) ==
    \A i \in 1..Len(subarray)-1 : subarray[i] <= subarray[i+1]

DoneInvariant ==
    pc = "Done" => Sorted(a)

=============================================================================