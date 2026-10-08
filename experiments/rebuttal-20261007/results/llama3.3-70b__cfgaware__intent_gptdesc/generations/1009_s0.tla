--------------------------- MODULE BufferedRandomAccessFile ---------------------------
EXTENDS Integers, Sequences

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz
VARIABLES file, buffer, dirty, offset, length, fp

TypeOK == (file \in [1..MaxOffset -> Symbols]) /\ 
          (buffer \in [1..BuffSz -> Symbols]) /\ 
          (dirty \in BOOLEAN) /\ 
          (offset \in 1..MaxOffset) /\ 
          (length \in 0..MaxOffset) /\ 
          (fp \in 0..MaxOffset)

Inv1 == dirty => offset + BuffSz <= length

Inv2CanAlwaysBeRestored == 
  IF dirty THEN 
    <<buffer := [i \in 1..BuffSz |-> file[(offset + i - 1) % MaxOffset]];
      dirty := FALSE;
      offset := fp>> 
  ELSE 
    <<buffer := [i \in 1..BuffSz |-> file[(offset + i - 1) % MaxOffset]]>> 

Inv3 == (file =<<|##|>>[i \in 1..length |-> IF i <= offset + BuffSz - 1 THEN buffer[i - offset] ELSE file[i]]) /\ 
         (length = Len(file))

Inv4 == fp <= length

Inv5 == dirty => offset + BuffSz > length

Spec == 
  /\ TypeOK
  /\ [][
      \/ \E s \in Symbols : 
        <>(seek(fp := fp + 1) /\ SeekCorrect)
      \/ \E s \in Symbols : 
        <>(setLength(length := length + 1) /\ (length' = length + 1))
      \/ \E bs \in Seq(Symbols) : 
        <>(read(bs) /\ ReadCorrect)
      \/ \E bs \in Seq(Symbols) : 
        <>(write(bs) /\ WriteAtMostCorrect)
      \/ <>FlushBuffer
    ]
  /\ WF_vars(<<seek, setLength, read, write, FlushBuffer>>)

SeekCorrect == 
  (fp' = fp + 1) /\ (file' = file) /\ (buffer' = buffer) /\ 
  (dirty' = dirty) /\ (offset' = offset) /\ (length' = length)

FlushBufferCorrect == 
  /\ (file' = [i \in 1..MaxOffset |-> IF i < offset OR i >= offset + BuffSz THEN file[i] ELSE buffer[i - offset]])
  /\ (buffer' = buffer)
  /\ (dirty' = FALSE)
  /\ (offset' = offset)
  /\ (length' = length)

SeekEstablishesInv2 == 
  /\ Inv2CanAlwaysBeRestored
  /\ (file' = file)
  /\ (buffer' = [i \in 1..BuffSz |-> file[(fp + i - 1) % MaxOffset]])
  /\ (dirty' = FALSE)
  /\ (offset' = fp)
  /\ (length' = length)

Write1Correct == 
  /\ (file' = [i \in 1..MaxOffset |-> IF i = fp THEN ArbitrarySymbol ELSE file[i]])
  /\ (buffer' = [i \in 1..BuffSz |-> IF i = fp - offset + 1 THEN ArbitrarySymbol ELSE buffer[i]])
  /\ (dirty' = TRUE)
  /\ (offset' = offset)
  /\ (length' = length)

Read1Correct == 
  /\ (file' = file)
  /\ (buffer' = buffer)
  /\ (dirty' = dirty)
  /\ (offset' = offset)
  /\ (length' = length)

WriteAtMostCorrect == 
  /\ (file' = [i \in 1..MaxOffset |-> IF i >= fp AND i < fp + Len(bs) THEN bs[i - fp] ELSE file[i]])
  /\ (buffer' = [i \in 1..BuffSz |-> IF i >= fp - offset + 1 AND i <= fp - offset + Len(bs) THEN bs[i - fp + offset - 1] ELSE buffer[i]])
  /\ (dirty' = TRUE)
  /\ (offset' = offset)
  /\ (length' = length)

ReadCorrect == 
  /\ (file' = file)
  /\ (buffer' = buffer)
  /\ (dirty' = dirty)
  /\ (offset' = offset)
  /\ (length' = length)

Safety == []Inv1 /\ []Inv2CanAlwaysBeRestored /\ []Inv3 /\ []Inv4 /\ []Inv5

THEOREM Spec => Safety
=============================================================================