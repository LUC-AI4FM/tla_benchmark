------------------------------ MODULE RegionMap ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
This module specifies the mapping between TLA+ and PlusCal (PCal) code regions,
focusing on the translation of syntactic regions and their correspondence.
It defines data structures for locations, regions, and translation objects,
and provides predicates for well-formedness and ordering of these objects.

It includes a PlusCal algorithm that, given a region in the TLA+ spec,
computes the corresponding token positions and analyzes parenthesis depth,
ensuring correct mapping and well-formedness, with assertions to check these
properties during execution.
*)

(*
--algorithm MapAlgo
variable
  \* Nondeterministically chosen input text (bounded length) and region.
  text \in Texts,
  region \in Regions(text),

  \* Scanning state.
  idx    = region.start,
  depth  = 0,
  stack  = <<>>,
  tokPos = <<>>,

  \* Properties computed/checked by the algorithm.
  okParen = TRUE,
  orderOK = TRUE;

begin
  scan:
    while idx <= region.end do
      tokPos := Append(tokPos, idx);

      if text[idx] \in OPEN then
        depth := depth + 1;
        stack := Append(stack, text[idx]);
      elsif text[idx] \in CLOSE then
        if Len(stack) = 0 \/ MATCH[text[idx]] # stack[Len(stack)] then
          okParen := FALSE;
        else
          depth := depth - 1;
          stack := SubSeq(stack, 1, Len(stack) - 1);
        end if;
      end if;

      idx := idx + 1;
    end while;

  done:
    orderOK :=
      /\ region.start <= region.end + 1
      /\ (tokPos =
            IF region.start <= region.end
            THEN [i \in 1..(region.end - region.start + 1) |-> region.start + i - 1]
            ELSE << >>)
      /\ \A i \in DOMAIN tokPos: tokPos[i] \in 1..Len(text);

    assert okParen = (Len(stack) = 0) message "Parentheses mismatch detected";
    assert orderOK message "Token order or bounds violated";
end algorithm;
*)

(***************************************************************************)
(*************************** Syntax and Types ******************************)
(***************************************************************************)

MaxLen == 4

OPEN  == {"(", "[", "{"}
CLOSE == {")", "]", "}"}
CHAR  == OPEN \cup CLOSE \cup {"a", "b"}

MATCH == [")" |-> "(", "]" |-> "[", "}" |-> "{"]

IsOpen(c)  == c \in OPEN
IsClose(c) == c \in CLOSE
IsMatch(o, c) == /\ o \in OPEN /\ c \in CLOSE /\ MATCH[c] = o

Texts == { s \in Seq(CHAR) : Len(s) <= MaxLen }

IsLocation(loc) ==
  /\ loc \in [pos : Nat, line : Nat, col : Nat]
  /\ loc.pos \in Nat /\ loc.line \in Nat /\ loc.col \in Nat

IsRegion(t, r) ==
  /\ r \in [start : 1..(Len(t) + 1), end : 0..Len(t)]
  /\ r.start <= r.end + 1

Regions(t) ==
  { [start |-> s, end |-> e] :
      /\ s \in 1..(Len(t) + 1)
      /\ e \in 0..Len(t)
      /\ s <= e + 1 }

IsTrans(tr, tlaLen, pcalLen) ==
  /\ tr \in [ tlaStart : 1..(tlaLen + 1),
              tlaEnd   : 0..tlaLen,
              pcalStart: 1..(pcalLen + 1),
              pcalEnd  : 0..pcalLen ]
  /\ tr.tlaStart <= tr.tlaEnd + 1
  /\ tr.pcalStart <= tr.pcalEnd + 1

IsStrictlyIncreasing(s) ==
  \A i \in 1..(IF Len(s)=0 THEN 0 ELSE Len(s)-1) : s[i] < s[i+1]

RegionToTokenMappingOK(t, r, tp) ==
  LET expected ==
        IF r.start <= r.end
        THEN [ i \in 1..(r.end - r.start + 1) |-> r.start + i - 1 ]
        ELSE << >>
  IN /\ tp = expected
     /\ \A i \in DOMAIN tp : tp[i] \in 1..Len(t)

TokensOrdered(tp) == IsStrictlyIncreasing(tp)

(***************************************************************************)
(******************** TLA+ translation of the PlusCal **********************)
(***************************************************************************)

VARIABLES
  pc,            \* control location
  text,          \* input sequence of characters/tokens
  region,        \* record [start, end] describing the region in 'text'
  idx,           \* current index into 'text' while scanning the region
  depth,         \* parenthesis nesting depth
  stack,         \* stack of opening parentheses (as a sequence)
  tokPos,        \* sequence of token positions collected from region
  okParen,       \* boolean flag that remains TRUE if no mismatch is observed
  orderOK        \* boolean computed at the end to summarize mapping/order

vars == << pc, text, region, idx, depth, stack, tokPos, okParen, orderOK >>

MapAlgoInit ==
  /\ pc = "scan"
  /\ text \in Texts
  /\ region \in Regions(text)
  /\ idx = region.start
  /\ depth = 0
  /\ stack = << >>
  /\ tokPos = << >>
  /\ okParen = TRUE
  /\ orderOK = TRUE

ScanStep ==
  /\ pc = "scan"
  /\ idx <= region.end
  /\ LET ch == text[idx] IN
       /\ tokPos' = Append(tokPos, idx)
       /\ IF ch \in OPEN THEN
            /\ depth' = depth + 1
            /\ stack' = Append(stack, ch)
            /\ okParen' = okParen
          ELSE IF ch \in CLOSE THEN
            LET good == (Len(stack) > 0) /\ (MATCH[ch] = stack[Len(stack)]) IN
              /\ okParen' = okParen /\ good
              /\ depth'   = depth - IF good THEN 1 ELSE 0
              /\ stack'   = IF good THEN SubSeq(stack, 1, Len(stack) - 1) ELSE stack
          ELSE
            /\ depth' = depth
            /\ stack' = stack
            /\ okParen' = okParen
  /\ idx' = idx + 1
  /\ pc' = IF idx' <= region.end THEN "scan" ELSE "done"
  /\ UNCHANGED << text, region, orderOK >>

DoneStep ==
  /\ pc = "done"
  /\ LET expected ==
        IF region.start <= region.end
        THEN [ i \in 1..(region.end - region.start + 1) |-> region.start + i - 1 ]
        ELSE << >>
     IN
     /\ orderOK' =
          /\ region.start <= region.end + 1
          /\ tokPos = expected
          /\ \A i \in DOMAIN tokPos : tokPos[i] \in 1..Len(text)
     /\ Assert(okParen = (Len(stack) = 0), "Parentheses mismatch detected")
     /\ Assert(orderOK', "Token order or bounds violated")
     /\ pc' = "end"
     /\ UNCHANGED << text, region, idx, depth, stack, tokPos, okParen >>

EndStep ==
  /\ pc = "end"
  /\ UNCHANGED vars

MapAlgoNext == ScanStep \/ DoneStep \/ EndStep

MapAlgoSpec == MapAlgoInit /\ [][MapAlgoNext]_vars

(***************************************************************************)
(**************************** Invariants/Props *****************************)
(***************************************************************************)

TypeInv ==
  /\ text \in Texts
  /\ region \in Regions(text)
  /\ idx \in 1..(Len(text) + 1)
  /\ depth \in Nat
  /\ stack \in Seq(OPEN)
  /\ tokPos \in Seq(1..Len(text))
  /\ okParen \in BOOLEAN
  /\ orderOK \in BOOLEAN
  /\ pc \in {"scan", "done", "end"}

TypeOK == TypeInv

ParenOK ==
  (pc = "end") => (okParen = (Len(stack) = 0))

MappingOK ==
  (pc = "end") => RegionToTokenMappingOK(text, region, tokPos)

(***************************************************************************)
(******************************* Aliases ***********************************)
(***************************************************************************)

Init == MapAlgoInit
Next == MapAlgoNext
Spec == MapAlgoSpec

=============================================================================