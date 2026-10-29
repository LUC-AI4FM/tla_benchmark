```tla
-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract RandomAccessFile specification over the logical file.          *)
(***************************************************************************)
AbsInit ==
    /\ absPointer = 0
    /\ absLength \in Offsets
    /\ result = NoResult

AWrite(s) ==
    LET p == absPointer
        n == Len(s)
    IN  /\ p + n <= MaxOffset
        /\ absPointer' = p + n
        /\ absLength'  = Max(absLength, p + n)
        /\ \A i \in FileIdx :
              /\ (p <= i /\ i < p + n) => absContent'[i] = s[i - p + 1]
              /\ (i < absLength /\ ~(p <= i /\ i < p + n))
                    => absContent'[i] = absContent[i]
        /\ UNCHANGED result

ARead(k) ==
    LET avail == absLength - absPointer
    IN  /\ absLength' = absLength
        /\ Agree(absContent', absContent, absLength)
        /\ IF avail <= 0
             THEN /\ result' = EOFResult
                  /\ absPointer' = absPointer
             ELSE LET n == Min(k, avail)
                  IN  /\ result' = DataResult([j \in 1..n |->
                                        absContent[absPointer + j - 1]])
                      /\ absPointer' = absPointer + n

ASeek(p) ==
    /\ absPointer' = p
    /\ absLength'  = absLength
    /\ Agree(absContent', absContent, absLength)
    /\ UNCHANGED result

ASetLength(n) ==
    /\ absLength'  = n
    /\ absPointer' = IF absPointer > n THEN n ELSE absPointer
    /\ Agree(absContent', absContent, Min(n, absLength))
    /\ UNCHANGED result

ANext ==
    \/ \E s \in AllWrites : AWrite(s)
    \/ \E k \in 1..BuffSz : ARead(k)
    \/ \E p \in Offsets : ASeek(p)
    \/ \E n \in Offsets : ASetLength(n)

AbsSpec == AbsInit /\ [][ANext]_AbsVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete buffered implementation.                                       *)
(***************************************************************************)

\* Refill the window starting at offset p from the underlying file
\* (whose length is fl). Leaves the disk pointer at the end of the bytes read.
RefillAt(p, fl) ==
    LET h == Max(p, Min(p + BuffSz, fl))
    IN  /\ lo'   = p
        /\ curr' = p
        /\ hi'   = h
        /\ file_pointer' = h
        /\ buff' = [j \in BuffIdx |->
                      IF p + j < h THEN file_content[p + j] ELSE buff[j]]

Init ==
    /\ file_length \in Offsets
    /\ file_content \in [FileIdx -> Symbols]
    /\ lo   = 0
    /\ curr = 0
    /\ hi   = Min(BuffSz, file_length)
    /\ file_pointer = Min(BuffSz, file_length)
    /\ buff = [j \in BuffIdx |->
                 IF j < Min(BuffSz, file_length)
                   THEN file_content[j] ELSE ArbitrarySymbol]
    /\ dirty  = FALSE
    /\ length = file_length
    /\ result = NoResult

\* Multi-byte write, served entirely within the cached window.
WriteBytes(s) ==
    LET n   == Len(s)
        off == curr - lo
    IN  /\ n >= 1
        /\ curr + n <= lo + BuffSz
        /\ curr + n <= MaxOffset
        /\ buff' = [j \in BuffIdx |->
                      IF off <= j /\ j < off + n
                        THEN s[j - off + 1] ELSE buff[j]]
        /\ hi'     = Max(hi, curr + n)
        /\ curr'   = curr + n
        /\ dirty'  = TRUE
        /\ length' = Max(length, curr + n)
        /\ UNCHANGED <<file_content, file_length, file_pointer, lo, result>>

\* Single-byte write
WriteByte(d) == WriteBytes(<<d>>)

\* Multi-byte read, served entirely within the cached window.
ReadBytes(k) ==
    /\ curr + k <= lo + BuffSz
    /\ LET avail == Min(hi, length) - curr
       IN  IF avail <= 0
             THEN /\ result' = EOFResult
                  /\ UNCHANGED curr
             ELSE LET n == Min(k, avail)
                  IN  /\ result' = DataResult([j \in 1..n |->
                                        buff[curr - lo + j - 1]])
                      /\ curr' = curr + n
    /\ UNCHANGED <<file_content, file_length, file_pointer, buff, dirty,
                   lo, hi, length>>

\* Single-byte read
ReadByte == ReadBytes(1)

\* Seek: inside the window just move the pointer; outside the window the
\* buffer must be clean (flushed) and is then refilled at the new position.
Seek(p) ==
    \/ /\ lo <= p /\ p < lo + BuffSz
       /\ curr' = p
       /\ UNCHANGED <<file_content, file_length, file_pointer, buff, dirty,
                      lo, hi, length, result>>
    \/ /\ ~(lo <= p /\ p < lo + BuffSz)
       /\ ~dirty
       /\ RefillAt(p, file_length)
       /\ UNCHANGED <<file_content, file_length, dirty, length, result>>

\* Flush: copy buffered bytes to the underlying file and clear dirty.
Flush ==
    /\ dirty
    /\ file_content' = [i \in FileIdx |->
                          IF lo <= i /\ i < hi
                            THEN buff[i - lo] ELSE file_content[i]]
    /\ file_length'  = Max(file_length, hi)
    /\ file_pointer' = hi
    /\ dirty' = FALSE
    /\ UNCHANGED <<buff, lo, hi, curr, length, result>>

\* setLength: requires a clean buffer. Truncates or extends the file
\* (extended contents are unspecified), clamps the pointer to the new
\* length per the RandomAccessFile contract, then refills the window.
SetLength(n) ==
    /\ ~dirty
    /\ file_length' = n
    /\ length' = n
    /\ RefillAt(Min(curr, n), n)
    /\ UNCHANGED <<file_content, dirty, result>>

\* Internal step: refill the window when the pointer has reached its end.
RestoreWindow ==
    /\ ~dirty
    /\ curr = lo + BuffSz
    /\ RefillAt(curr, file_length)
    /\ UNCHANGED <<file_content, file_length, dirty, length, result>>

Next ==
    \/ \E d \in Symbols : WriteByte(d)
    \/ \E s \in MultiWrites : WriteBytes(s)
    \/ ReadByte
    \/ \E k \in 2..BuffSz : ReadBytes(k)
    \/ \E p \in Offsets : Seek(p)
    \/ \E n \in Offsets : SetLength(n)
    \/ Flush
    \/ RestoreWindow

Spec == Init /\ [][Next]_vars /\ WF_vars(Flush) /\ WF_vars(RestoreWindow)

-----------------------------------------------------------------------------
(***************************************************************************)
(* (1) Internal invariants.                                                *)
(***************************************************************************)
TypeOK ==
    /\ file_content \in [FileIdx -> Symbols]
    /\ file_length \in Offsets
    /\ file_pointer \in Offsets
    /\ buff \in [BuffIdx -> Symbols]
    /\ dirty \in BOOLEAN
    /\ lo \in Offsets
    /\ hi \in Offsets
    /\ curr \in Offsets
    /\ length \in Offsets
    /\ result \in Results

\* Window bounds
WindowBounds ==
    /\ lo <= curr /\ curr <= lo + BuffSz
    /\ lo <= hi   /\ hi <= lo + BuffSz
    /\ hi <= MaxOffset

\* The window is full, or it reaches the end of the underlying file
WindowFill == hi = lo + BuffSz \/ hi >= file_length

\* A dirty buffer holds at least one written byte
DirtyNonEmpty == dirty => hi > lo

\* Logical length is the underlying length, extended by buffered writes
LengthInv ==
    length = IF dirty THEN Max(file_length, hi) ELSE file_length

\* A clean buffer mirrors the underlying file exactly
CleanBuffer ==
    ~dirty =>
        /\ (hi = lo \/ hi <= file_length)
        /\ \A i \in lo..(hi - 1) : buff[i - lo] = file_content[i]

\* The logical file equals the underlying file updated by buffered bytes
LogicalContentInv ==
    \A i \in 0..(length - 1) :
        absContent[i] = IF lo <= i /\ i < hi
                          THEN buff[i - lo] ELSE file_content[i]

\* Relationship between the disk pointer and the window after flush/fill
PointerInv ==
    /\ lo <= file_pointer /\ file_pointer <= hi
    /\ ~dirty => file_pointer = hi

\* A dirty buffer can always be flushed, and a clean buffer can always be
\* repositioned/refilled, so restoring sequences are always possible.
FlushRestorable ==
    /\ dirty => ENABLED Flush
    /\ ~dirty => \A p \in Offsets : ENABLED Seek(p)

Invariants ==
    /\ TypeOK
    /\ WindowBounds
    /\ WindowFill
    /\ DirtyNonEmpty
    /\ LengthInv
    /\ CleanBuffer
    /\ LogicalContentInv
    /\ PointerInv
    /\ FlushRestorable

-----------------------------------------------------------------------------
(***************************************************************************)
(* (2) Refinement of the abstract RandomAccessFile specification.          *)
(***************************************************************************)
Refinement == AbsSpec

(***************************************************************************)
(* (3) Each concrete operation refines its abstract counterpart.           *)
(***************************************************************************)
OpRefinement ==
    [][ /\ \A d \in Symbols : WriteByte(d) => AWrite(<<d>>)
        /\ \A s \in MultiWrites : WriteBytes(s) => AWrite(s)
        /\ ReadByte => ARead(1)
        /\ \A k \in 2..BuffSz : ReadBytes(k) => ARead(k)
        /\ \A p \in Offsets : Seek(p) => ASeek(p)
        /\ \A n \in Offsets : SetLength(n) => ASetLength(n)
        /\ Flush => UNCHANGED AbsVars
        /\ RestoreWindow => UNCHANGED AbsVars
      ]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: a dirty buffer is eventually flushed, and an exhausted        *)
(* window is eventually restored.                                          *)
(***************************************************************************)
DirtyEventuallyFlushed == dirty ~> ~dirty

WindowRestored == (curr = lo + BuffSz) ~> (curr < lo + BuffSz)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => Refinement
THEOREM Spec => OpRefinement
THEOREM Spec => DirtyEventuallyFlushed /\ WindowRestored
=============================================================================
```