MODULE BufferedRandomAccessFile
EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxFileSize, BufSize, ArbitrarySymbol

VARIABLES pos, logLen, bufStart, bufLen, buffer, dirty, fileData

(* Derived definitions *)
LogicalByte(i) ==
  IF dirty /\ (i >= bufStart /\ i < bufStart + bufLen)
    THEN buffer[i - bufStart]
    ELSE fileData[i]

Init ==
  /\ pos = 0
  /\ logLen = 0
  /\ bufStart = 0
  /\ bufLen = 0
  /\ buffer = [i \in 0..BufSize-1 |-> ArbitrarySymbol]
  /\ dirty = FALSE
  /\ fileData = [i \in 0..MaxFileSize-1 |-> ArbitrarySymbol]

Seek(newPos) ==
  /\ newPos >= 0
  /\ newPos <= logLen
  /\ pos' = newPos

Read(n) ==
  LET newBufStart == pos
      newBufLen   == Min(BufSize, logLen - pos)
      newBuffer   == [i \in 0..BufSize-1 |
                      i < newBufLen -> LogicalByte(pos + i)
                     \/ TRUE -> ArbitrarySymbol]
  IN
    /\ n >= 0
    /\ pos + n <= logLen
    /\ pos' = pos + n
    /\ bufStart' = newBufStart
    /\ bufLen'   = newBufLen
    /\ buffer'   = newBuffer
    /\ dirty'    = FALSE

Write(data) ==
  LET d == data, n == Len(d)
  IN
    /\ n >= 0
    /\ pos + n <= MaxFileSize
    /\ dirty'    = TRUE
    /\ bufStart' = pos
    /\ bufLen'   = n
    /\ buffer'   = [i \in 0..BufSize-1 |
                     i < n -> d[i+1]
                    \/ TRUE -> ArbitrarySymbol]
    /\ logLen'   = IF pos + n > logLen THEN pos + n ELSE logLen
    /\ pos'      = pos + n

Flush ==
  /\ dirty
  LET newFileData == [i \in 0..MaxFileSize-1 |
                      i >= bufStart /\ i < bufStart + bufLen -> buffer[i - bufStart]
                     \/ TRUE -> fileData[i] ]
  IN
    /\ fileData' = newFileData
    /\ dirty'    = FALSE

SetLength(len) ==
  /\ len >= 0
  /\ len <= MaxFileSize
  /\ logLen'   = len
  /\ pos'      = IF pos > len THEN len ELSE pos
  /\ dirty'    = FALSE
  /\ bufStart' = 0
  /\ bufLen'   = 0
  /\ buffer'   = [i \in 0..BufSize-1 |-> ArbitrarySymbol]

Next ==
  \/ \E newPos \in 0..logLen : Seek(newPos)
  \/ \E n \in Nat        : Read(n)
  \/ \E data \in Seq(ANY) : Write(data)
  \/ Flush
  \/ \E len \in 0..MaxFileSize : SetLength(len)

SafetyInv ==
  /\ pos >= 0
  /\ pos <= logLen
  /\ bufStart >= 0
  /\ bufStart < MaxFileSize
  /\ bufLen >= 0
  /\ bufLen <= BufSize
  /\ dirty \in BOOLEAN
  /\ logLen >= 0
  /\ logLen <= MaxFileSize

Spec == Init /\ [][Next]_<<pos, logLen, bufStart, bufLen, buffer, dirty, fileData>> /\ SafetyInv

===============================================================================