--------------------------- MODULE test64 ---------------------------
\* Changed module name casing because the prior form had become illegal.
VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec
=============================================================================