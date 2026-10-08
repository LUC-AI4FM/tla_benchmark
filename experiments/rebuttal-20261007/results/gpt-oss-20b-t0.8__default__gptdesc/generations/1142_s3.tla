```
MODULE RegionMapping
EXTENDS Naturals, Sequences, TLC

(* Record type definitions (for documentation only) *)
(* Token is a record [txt : Seq Char, start : Nat, end : Nat]        *)
(* Region is a record [start : Nat, end : Nat]                       *)
(* Translation is a record [region : Region, tokenIndices : <<Nat>>] *)

VARIABLES text, tokens, regions, translations

Init ==
   /\ text = <<>>
   /\ tokens = <<>>
   /\ regions = <<>>
   /\ translations = <<>>

ParenthesisDepthPrefix(i) ==
   IF i = 0 THEN
      0
   ELSE
      Sum(1..i,
          \j -> (CASE text[j] OF
                   "(" -> 1
                 \_ -> (CASE text[j] OF ")" -> -1 | _ -> 0)))

ParenthesisInvariant ==
   /\ \A i \in 0..Len(text) : ParenthesisDepthPrefix(i) >= 0
   /\ ParenthesisDepthPrefix(Len(text)) = 0

ComputeTranslations ==
    LET newTrans == Seq({ t :
            r \in regions |
            LET inds == { j \in 1..Len(tokens) :
                           tokens[j].start >= r.start /\ tokens[j].end <= r.end } IN
                [region |-> r, tokenIndices |-> <<j \in inds>>] })
    IN translations' = newTrans

Next ==
   ComputeTranslations

MappingInvariant ==
   \A t \in translations :
       \A idx \in t.tokenIndices :
          tokens[idx].start >= t.region.start /\ tokens[idx].end <= t.region.end

Spec ==
   Init
   /\ [][Next]_(<<text, tokens, regions, translations>>
   /\ ParenthesisInvariant
   /\ MappingInvariant
```