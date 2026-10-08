MODULE SimpleUpdate
EXTENDS Naturals, Sequences, Integers

CONSTANTS InitSet, InitSeq, NewSymbol, NewInt

VARIABLES S, Seq

(* Derived constants *)
SymbolSet == InitSet ∪ {NewSymbol}
FinalSet   == SymbolSet
FinalSeq   == <<InitSeq[1], NewInt, InitSeq[3]>>

(* Initial state *)
Init ==
  /\ S = InitSet
  /\ Seq = InitSeq

(* Update step *)
Update ==
  /\ S' = S \cup {NewSymbol}
  /\ Seq' = <<Seq[1], NewInt, Seq[3]>> 
  /\ NewSymbol \notin S

(* Stuttering step *)
Stutter ==
  /\ S' = S
  /\ Seq' = Seq

Next ==
  IF (S = FinalSet /\ Seq = FinalSeq) THEN Stutter ELSE Update

TypeInvariant ==
  /\ S \subseteq SymbolSet
  /\ Len(Seq) = 3
  /\ \A i \in {1,2,3} : Seq[i] ∈ Int

Safety == TypeInvariant

Liveness == <> (S = FinalSet /\ Seq = FinalSeq)

Spec == Init /\ [][Next]_<<S, Seq>> /\ Liveness

END MODULE