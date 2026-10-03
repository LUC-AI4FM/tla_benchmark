---- MODULE PlusCalTranslator ----
EXTENDS TLC, Sequences, FiniteSets, Bags, Any

CONSTANT Object
\* This specification models the translation of a PlusCal AST into a TLA+
\* specification. The CONSTANT `Object` represents the universe of primitive
\* values that can appear in the AST, such as identifiers and literal values.
\* For model checking, it would be instantiated, e.g., `Object <- {"x", "y", 1, 2}`.

\* We assume STRING and Int are subsets of Object for this specification.
ASSUME IsFiniteSet(Object)

\*=============================================================================