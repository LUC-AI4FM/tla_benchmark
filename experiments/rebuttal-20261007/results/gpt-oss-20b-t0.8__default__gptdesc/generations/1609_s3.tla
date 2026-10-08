MODULE QuickSort

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ArrayLen, InitialArray
(* Assume InitialArray : [1 .. ArrayLen -> Nat] *)

VARIABLES A, pc, stack

(*** Helper definitions ***)

ValidFrame(f) == f \in [l:Nat, r:Nat] /\ 1 <= f.l /\ f.r <= ArrayLen

StackInvariant == ALL i \in DOMAIN stack : ValidFrame(stack[i])

Count(v,X) == Cardinality({i \in 1 .. ArrayLen : X[i] = v})

Permutation(X,Y) == ∀v \in Nat : Count(v, X) = Count(v, Y)

Partitioned(X,l,r,p) ==
    ∀ i \in 1 .. ArrayLen :
        ((i >= l /\ i <= p) => X[i] <= X[p]) /\
        ((i > p /\ i <= r) => X[i] >= X[p])

OutsideUnchanged(X,Y,l,r) ==
    ∀ k \in 1 .. ArrayLen : (k < l \/ k > r) => Y[k] = X[k]

(*** Initial state ***)

Init == 
    pc = "Init" /\ stack = <<>> /\ A = InitialArray

(*** Actions ***)

InitStep ==
   /\ pc = "Init"
   /\ stack = <<>>
   /\ A' = A
   /\ pc' = "QS"
   /\ stack' = <<[l: 1, r: ArrayLen]>>

QSPop ==
   /\ pc = "QS"
   /\ stack # <<>>
   /\ LET f == Head(stack) IN f.l >= f.r
   /\ pc' = pc
   /\ stack' = Tail(stack)
   /\ A' = A

QSPivot(p) ==
   /\ pc = "QS"
   /\ stack # <<>>
   /\ LET f == Head(stack) IN f.l < f.r /\ f.l <= p /\ p <= f.r
   /\ Permutation(A, A')
   /\ Partitioned(A', f.l, f.r, p)
   /\ OutsideUnchanged(A, A', f.l, f.r)
   /\ LET left  == [l: f.l, r: p-1]
          right == [l: p+1, r: f.r]
          rest  == Tail(stack)
          newStack1 == IF left.l <= left.r THEN <<left>> ++ rest ELSE rest
          newStack2 == IF right.l <= right.r THEN <<right>> ++ newStack1 ELSE newStack1
      IN stack' = newStack2 /\ pc' = pc /\ A' = A

DoneStep ==
   /\ pc = "QS"
   /\ stack = <<>>
   /\ pc' = "Done"
   /\ stack' = <<>>
   /\ A' = A

Stutter ==
   /\ pc = "Done"
   /\ pc' = pc
   /\ stack' = stack
   /\ A' = A

Next == InitStep \/ QSPop \/ (∃p \in 1 .. ArrayLen : QSPivot(p)) \/ DoneStep \/ Stutter

(*** Specification ***)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*** Invariant ***)

Invariant ==
    pc \in {"Init","QS","Done"} /\ StackInvariant

(*** Liveness Property: eventual termination ***) 

Termination == Spec => <> (pc = "Done")

End QuickSort