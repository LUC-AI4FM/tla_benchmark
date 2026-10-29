------------------------- MODULE BufferedRandomAccessFile -------------------------
(***************************************************************************)
(* Buffered random-access file, with an abstract RandomAccessFile         *)
(* refinement target and shared array/file utilities, in one module.      *)
(*                                                                         *)
(* The model is single-threaded and has no explicit fault model.  File    *)
(* contents that Java leaves unspecified (bytes created by extending a    *)
(* file) are represented by the constant ArbitrarySymbol.  This keeps the *)
(* model finite and checkable.                                            *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
    Symbols,          \* possible byte values
    ArbitrarySymbol,  \* stands for an unspecified byte value
    MaxOffset,        \* largest file offset / length considered
    BuffSz            \* size of the in-memory buffer

ASSUME /\ ArbitrarySymbol \notin Symbols
       /\ MaxOffset \in Nat
       /\ BuffSz \in Nat \ {0}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Shared array / file utilities                                          *)
(* An array of length n is a function with domain 0..(n-1).               *)
(***************************************************************************)
Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

Offset == 0..MaxOffset

SymbolOrArbitrary == Symbols \cup {ArbitrarySymbol}

EOF     == "EOF"
NoValue == "NoValue"

Len(a) == Cardinality(DOMAIN a)

IsArrayOf(a, T) ==
    /\ \E n \in 0..MaxOffset : DOMAIN a = 0..(n-1)
    /\ \A i \in DOMAIN a : a[i] \in T

EmptyArray == [i \in {} |-> ArbitrarySymbol]

\* Write value v at index i, extending with arbitrary bytes if necessary.
WriteAt(a, i, v) ==
    [j \in 0..(Max(Len(a), i + 1) - 1) |->
        IF j = i THEN v
        ELSE IF j < Len(a) THEN a[j]
        ELSE ArbitrarySymbol]

\* Truncate or extend (with arbitrary bytes) to length n.
SetLen(a, n) ==
    [j \in 0..(n - 1) |-> IF j < Len(a) THEN a[j] ELSE ArbitrarySymbol]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete state of the buffered file object                             *)
(***************************************************************************)
VARIABLES
    disk,     \* contents of the underlying on-disk file
    diskPos,  \* file pointer of the underlying file
    dirty,    \* buffer holds data not yet written to disk
    length,   \* logical length of the file
    curr,     \* logical file pointer
    lo,       \* buffer covers file positions lo..(hi-1)
    hi,
    buff,     \* the buffer itself: [0..BuffSz-1 -> bytes]
    ret       \* value returned by the last read (shared with abstract spec)

vars == <<disk, diskPos, dirty, length, curr, lo, hi, buff, ret>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping: the logical contents seen by clients.              *)
(***************************************************************************)
InBuffer(j) == lo <= j /\ j < hi

LogicalContent ==
    [j \in 0..(length - 1) |->
        IF InBuffer(j) THEN buff[j - lo]
        ELSE IF j < Len(disk) THEN disk[j]
        ELSE ArbitrarySymbol]

RAF_content == LogicalContent
RAF_pointer == curr

absVars == <<RAF_content, RAF_pointer, ret>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract RandomAccessFile specification (stated over the mapping)      *)
(***************************************************************************)
AbsInit ==
    /\ RAF_content = EmptyArray
    /\ RAF_pointer = 0
    /\ ret = NoValue

AbsSeek(p) ==
    /\ RAF_pointer' = p
    /\ RAF_content' = RAF_content
    /\ ret' = ret

AbsRead ==
    IF RAF_pointer < Len(RAF_content)
    THEN /\ ret' = RAF_content[RAF_pointer]
         /\ RAF_pointer' = RAF_pointer + 1
         /\ RAF_content' = RAF_content
    ELSE /\ ret' = EOF
         /\ RAF_pointer' = RAF_pointer
         /\ RAF_content' = RAF_content

AbsWrite(v) ==
    /\ RAF_pointer < MaxOffset
    /\ RAF_content' = WriteAt(RAF_content, RAF_pointer, v)
    /\ RAF_pointer' = RAF_pointer + 1
    /\ ret' = ret

AbsSetLength(n) ==
    /\ RAF_content' = SetLen(RAF_content, n)
    /\ RAF_pointer' = IF RAF_pointer > n THEN n ELSE RAF_pointer
    /\ ret' = ret

AbsNext ==
    \/ \E p \in Offset : AbsSeek(p)
    \/ AbsRead
    \/ \E v \in Symbols : AbsWrite(v)
    \/ \E n \in Offset : AbsSetLength(n)

AbsSpec == AbsInit /\ [][AbsNext]_absVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete helpers                                                       *)
(***************************************************************************)

\* Disk contents after writing the dirty part of the buffer.
WrittenDisk ==
    [j \in 0..(Max(Len(disk), hi) - 1) |->
        IF InBuffer(j) THEN buff[j - lo]
        ELSE IF j < Len(disk) THEN disk[j]
        ELSE ArbitrarySymbol]

FlushedDisk == IF dirty THEN WrittenDisk ELSE disk

FlushedDiskPos == IF dirty THEN hi ELSE diskPos

\* Fill a buffer from disk d starting at file position p.
LoadBuffer(d, p) ==
    [i \in 0..(BuffSz - 1) |->
        IF p + i < Len(d) THEN d[p + i] ELSE ArbitrarySymbol]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete initial state and operations                                  *)
(***************************************************************************)
Init ==
    /\ disk = EmptyArray
    /\ diskPos = 0
    /\ dirty = FALSE
    /\ length = 0
    /\ curr = 0
    /\ lo = 0
    /\ hi = 0
    /\ buff = [i \in 0..(BuffSz - 1) |-> ArbitrarySymbol]
    /\ ret = NoValue

\* seek(p): just moves the logical pointer; the buffer is handled lazily.
Seek(p) ==
    /\ curr' = p
    /\ UNCHANGED <<disk, diskPos, dirty, length, lo, hi, buff, ret>>

\* read(): serve from the buffer if possible, else flush and refill.
Read ==
    IF curr >= length
    THEN /\ ret' = EOF
         /\ UNCHANGED <<disk, diskPos, dirty, length, curr, lo, hi, buff>>
    ELSE IF InBuffer(curr)
    THEN /\ ret' = buff[curr - lo]
         /\ curr' = curr + 1
         /\ UNCHANGED <<disk, diskPos, dirty, length, lo, hi, buff>>
    ELSE LET d1  == FlushedDisk
             hi1 == Max(curr, Min(Len(d1), curr + BuffSz))
             b1  == LoadBuffer(d1, curr)
         IN  /\ disk' = d1
             /\ dirty' = FALSE
             /\ lo' = curr
             /\ hi' = hi1
             /\ buff' = b1
             /\ diskPos' = hi1
             /\ ret' = b1[0]
             /\ curr' = curr + 1
             /\ UNCHANGED length

\* write(v): write into the buffer if the position is reachable without a
\* gap, otherwise flush, refill at curr, and write there.
Write(v) ==
    /\ curr < MaxOffset
    /\ LET inBuf == lo <= curr /\ curr < lo + BuffSz /\ curr <= hi
           d1  == IF inBuf THEN disk ELSE FlushedDisk
           lo1 == IF inBuf THEN lo ELSE curr
           hi1 == IF inBuf THEN hi
                  ELSE Max(curr, Min(Len(d1), curr + BuffSz))
           b1  == IF inBuf THEN buff ELSE LoadBuffer(d1, curr)
           dp1 == IF inBuf THEN diskPos ELSE hi1
       IN  /\ disk' = d1
           /\ lo' = lo1
           /\ hi' = Max(hi1, curr + 1)
           /\ buff' = [b1 EXCEPT ![curr - lo1] = v]
           /\ dirty' = TRUE
           /\ length' = Max(length, curr + 1)
           /\ curr' = curr + 1
           /\ diskPos' = dp1
           /\ UNCHANGED ret

\* flush(): write dirty buffer contents to disk.
Flush ==
    /\ disk' = FlushedDisk
    /\ diskPos' = FlushedDiskPos
    /\ dirty' = FALSE
    /\ UNCHANGED <<length, curr, lo, hi, buff, ret>>

\* setLength(n): flush, change the underlying length, invalidate buffer.
SetLength(n) ==
    LET d1 == SetLen(FlushedDisk, n)
        c1 == IF curr > n THEN n ELSE curr
    IN  /\ disk' = d1
        /\ diskPos' = Min(FlushedDiskPos, n)
        /\ dirty' = FALSE
        /\ length' = n
        /\ curr' = c1
        /\ lo' = c1
        /\ hi' = c1
        /\ UNCHANGED <<buff, ret>>

Next ==
    \/ \E p \in Offset : Seek(p)
    \/ Read
    \/ \E v \in Symbols : Write(v)
    \/ Flush
    \/ \E n \in Offset : SetLength(n)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Internal invariants                                                    *)
(***************************************************************************)
TypeOK ==
    /\ IsArrayOf(disk, SymbolOrArbitrary)
    /\ diskPos \in Offset
    /\ dirty \in BOOLEAN
    /\ length \in Offset
    /\ curr \in Offset
    /\ lo \in Offset
    /\ hi \in Offset
    /\ buff \in [0..(BuffSz - 1) -> SymbolOrArbitrary]
    /\ ret \in SymbolOrArbitrary \cup {EOF, NoValue}

BufferRangeOK ==
    /\ lo <= hi
    /\ hi - lo <= BuffSz
    /\ hi <= length

DiskNotLongerThanLogical == Len(disk) <= length

LengthIsDiskOrBuffer == length = Max(Len(disk), hi)

CleanBufferMatchesDisk ==
    ~dirty => \A j \in lo..(hi - 1) : j < Len(disk) /\ buff[j - lo] = disk[j]

LogicalLengthOK == Len(LogicalContent) = length

FlushPreservesLogical ==
    [j \in 0..(length - 1) |->
        IF j < Len(FlushedDisk) THEN FlushedDisk[j] ELSE ArbitrarySymbol]
        = LogicalContent

Inv ==
    /\ TypeOK
    /\ BufferRangeOK
    /\ DiskNotLongerThanLogical
    /\ LengthIsDiskOrBuffer
    /\ CleanBufferMatchesDisk
    /\ LogicalLengthOK
    /\ FlushPreservesLogical

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement properties                                                  *)
(***************************************************************************)

\* The whole behavior refines the abstract RandomAccessFile spec.
RefinesAbstract == AbsSpec

\* Each concrete operation refines its abstract counterpart.
SeekRefines ==
    [][\A p \in Offset : Seek(p) => AbsSeek(p)]_vars

ReadRefines ==
    [][Read => AbsRead]_vars

WriteRefines ==
    [][\A v \in Symbols : Write(v) => AbsWrite(v)]_vars

FlushRefines ==
    [][Flush => UNCHANGED absVars]_vars

SetLengthRefines ==
    [][\A n \in Offset : SetLength(n) => AbsSetLength(n)]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking helpers                                                 *)
(***************************************************************************)
Perms == Permutations(Symbols)

Alias ==
    [ disk     |-> disk,
      diskPos  |-> diskPos,
      dirty    |-> dirty,
      length   |-> length,
      curr     |-> curr,
      lo       |-> lo,
      hi       |-> hi,
      buff     |-> buff,
      ret      |-> ret,
      logical  |-> LogicalContent ]

(***************************************************************************)
(* TLC configuration (BufferedRandomAccessFile.cfg):                      *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*       Symbols = {s1, s2}                                                *)
(*       ArbitrarySymbol = Arb                                             *)
(*       MaxOffset = 3                                                     *)
(*       BuffSz = 2                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   SYMMETRY Perms                                                        *)
(*   ALIAS Alias                                                           *)
(*   INVARIANTS                                                            *)
(*       TypeOK                                                            *)
(*       BufferRangeOK                                                     *)
(*       DiskNotLongerThanLogical                                          *)
(*       LengthIsDiskOrBuffer                                              *)
(*       CleanBufferMatchesDisk                                            *)
(*       LogicalLengthOK                                                   *)
(*       FlushPreservesLogical                                             *)
(*   PROPERTIES                                                            *)
(*       RefinesAbstract                                                   *)
(*       SeekRefines                                                       *)
(*       ReadRefines                                                       *)
(*       WriteRefines                                                      *)
(*       FlushRefines                                                      *)
(*       SetLengthRefines                                                  *)
(***************************************************************************)
=============================================================================