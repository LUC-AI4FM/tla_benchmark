---------------------------- MODULE test64 ----------------------------
\* Module name casing changed because the prior form had become illegal.

VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec

=============================================================================