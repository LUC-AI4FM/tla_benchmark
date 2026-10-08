---- MODULE BufferedRandomAccessFile ----
EXTENDS Naturals

CONSTANTS MaxOffset, BuffSz

(*
 State and basic domains
*)
VARIABLES dirty, length, curr, lo, buff, diskPos, file_content, file_pointer

Offset == 0..MaxOffset
BufIdx == 0..(BuffSz - 1)
Len == 0..(MaxOffset + 1)
Byte == 0..1

Vars == << dirty, length, curr, lo, buff, diskPos, file_content, file_pointer >>

(*
 Helper operators
*)
Window(loVal) ==
  { o \in Offset : loVal <= o /\ o < loVal + BuffSz }

BuildBuff(fc, loVal) ==
  [ i \in BufIdx |->
      IF loVal + i \in Offset
      THEN fc[loVal + i]
      ELSE 0 ]

LogicalFileContent ==
  [ o \in Offset |->
      IF o \in Window(lo)
      THEN buff[o - lo]
      ELSE file_content[o] ]

Range(pos, k) ==
  { o \in Offset : pos <= o /\ o < pos + k }

Skip ==
  UNCHANGED Vars

(*
 Typing and invariants
*)
TypeOK ==
  /\ dirty \in BOOLEAN
  /\ length \in Len
  /\ curr \in Offset
  /\ lo \in Offset
  /\ buff \in [BufIdx -> Byte]
  /\ diskPos \in 0..(MaxOffset + 1)
  /\ file_pointer \in 0..(MaxOffset + 1)
  /\ file_content \in [Offset -> Byte]

Inv1 ==
  /\ ~dirty
  => \A o \in Window(lo) : buff[o - lo] = file_content[o]

Inv2 ==
  curr \in Window(lo)

Inv3 ==
  \A o \in Offset :
    (o \notin Window(lo)) => LogicalFileContent[o] = file_content[o]

Inv4 ==
  /\ curr <= length
  /\ length \in Len

Inv5 ==
  diskPos = file_pointer

(*
 Actions
*)
FlushBuffer ==
  /\ dirty
  /\ file_content' =
       [ o \in Offset |->
           IF o \in Window(lo)
           THEN buff[o - lo]
           ELSE file_content[o] ]
  /\ dirty' = FALSE
  /\ lo' = lo
  /\ buff' = buff
  /\ curr' = curr
  /\ length' = length
  /\ diskPos' = lo
  /\ file_pointer' = diskPos'

Seek ==
  \E p \in Offset :
    IF p \in Window(lo) THEN
      /\ curr' = p
      /\ UNCHANGED << dirty, lo, buff, file_content, length, diskPos, file_pointer >>
    ELSE
      \E loN \in Offset :
        /\ p \in Window(loN)
        /\ IF dirty
             THEN file_content' =
                    [ o \in Offset |->
                        IF o \in Window(lo)
                        THEN buff[o - lo]
                        ELSE file_content[o] ]
             ELSE file_content' = file_content
        /\ lo' = loN
        /\ buff' = BuildBuff(file_content', lo')
        /\ curr' = p
        /\ dirty' = FALSE
        /\ length' = length
        /\ diskPos' = p
        /\ file_pointer' = diskPos'

SetLength ==
  \E L \in Len :
    /\ length' = L
    /\ curr' = IF curr > L THEN L ELSE curr
    /\ UNCHANGED << lo, buff, dirty, file_content, diskPos, file_pointer >>

Read1 ==
  /\ curr < length
  /\ curr < MaxOffset
  /\ curr \in Window(lo)
  /\ curr' = curr + 1
  /\ UNCHANGED << dirty, lo, buff, file_content, length, diskPos, file_pointer >>

Write1 ==
  /\ curr \in Window(lo)
  /\ buff' =
       [ i \in BufIdx |->
           IF lo + i = curr
           THEN CHOOSE v \in Byte : TRUE
           ELSE buff[i] ]
  /\ dirty' = TRUE
  /\ file_content' = file_content
  /\ lo' = lo
  /\ length' = IF curr = length /\ length < MaxOffset + 1 THEN length + 1 ELSE length
  /\ curr' = IF curr < MaxOffset THEN curr + 1 ELSE curr
  /\ diskPos' = diskPos
  /\ file_pointer' = file_pointer

Read ==
  \E n \in 0..BuffSz :
    /\ curr \in Window(lo)
    /\ LET k == IF n <= lo + BuffSz - curr THEN n ELSE lo + BuffSz - curr
       IN /\ curr' = curr + k
          /\ UNCHANGED << dirty, lo, buff, file_content, length, diskPos, file_pointer >>

WriteAtMost ==
  \E n \in 0..BuffSz :
    /\ curr \in Window(lo)
    /\ LET k == IF n <= lo + BuffSz - curr THEN n ELSE lo + BuffSz - curr
       IN /\ buff' =
              [ i \in BufIdx |->
                  IF (lo + i) >= curr /\ (lo + i) < curr + k
                  THEN CHOOSE v \in Byte : TRUE
                  ELSE buff[i] ]
          /\ dirty' = TRUE
          /\ curr' = curr + k
          /\ UNCHANGED << file_content, lo, length, diskPos, file_pointer >>

Next ==
  FlushBuffer \/ Seek \/ SetLength \/ Read1 \/ Write1 \/ Read \/ WriteAtMost

Init ==
  /\ file_content \in [Offset -> Byte]
  /\ dirty = FALSE
  /\ lo = 0
  /\ buff = BuildBuff(file_content, lo)
  /\ curr = 0
  /\ length \in Len
  /\ diskPos = 0
  /\ file_pointer = diskPos

Spec ==
  Init /\ [][Next]_Vars

(*
 Symbols for model convenience
*)
Symbols ==
  {"FlushBuffer","Seek","SetLength","Read1","Write1","Read","WriteAtMost"}

ArbitrarySymbol ==
  CHOOSE s \in Symbols : TRUE

(*
 Correctness and liveness-style properties
*)
Safety ==
  TypeOK /\ [](TypeOK /\ Inv1 /\ Inv3 /\ Inv4 /\ Inv5)

FlushBufferCorrect ==
  [] (FlushBuffer => LogicalFileContent' = file_content')

SeekCorrect ==
  [] (Seek => LogicalFileContent' = LogicalFileContent)

SeekEstablishesInv2 ==
  [] (Seek => Inv2')

Inv2CanAlwaysBeRestored ==
  LET FlushThenSeekEnabled ==
        ENABLED (IF dirty THEN FlushBuffer ELSE Skip) /\ ENABLED Seek
  IN [] (~Inv2 => FlushThenSeekEnabled)

Write1Correct ==
  [] ( Write1
       => /\ curr' = IF curr < MaxOffset THEN curr + 1 ELSE curr
          /\ \A o \in Offset : o # curr => LogicalFileContent'[o] = LogicalFileContent[o] )

Read1Correct ==
  [] ( Read1
       => /\ LogicalFileContent' = LogicalFileContent
          /\ curr' = curr + 1 )

WriteAtMostCorrect ==
  [] ( WriteAtMost
       => \E k \in 0..BuffSz :
            /\ curr' = curr + k
            /\ \A o \in Offset :
                 (o \notin Range(curr, k)) => LogicalFileContent'[o] = LogicalFileContent[o] )

ReadCorrect ==
  [] ( Read
       => /\ LogicalFileContent' = LogicalFileContent
          /\ curr' >= curr
          /\ curr' <= curr + BuffSz )

====