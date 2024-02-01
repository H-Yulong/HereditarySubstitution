# Hereditary Substitution
A formalization of hereditary substitution for STLC, in a "continuation-passing" style that makes it structurally recursive.

### Repo
Basic.agda - small library of basic things

Syntax.agda - Syntax of STLC and normal forms

Stack.agda - Hereditary substitution, in terms of stacks and normal forms (NF)

Spine.agda - Hereditary substitution, using normal forms with spines (SNF)

ProofsInv.agda - Correctness proofs of the normalization in Spine, using invertible beta-eta equalities.

SProof.agda - Proof that NF is isomorphic to SNF, and the correctness properties transport to NF.

Lemmas.agda - Lemmas for proofs in ProofsInv.
