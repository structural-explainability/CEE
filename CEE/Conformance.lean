import CEE.Spec.IdentifierMap

namespace CEE.Conformance

/-!
# CEE Conformance Predicate (v1)

This file provides a proof-carrying conformance interface for CEE using the
stable requirement identifiers defined in IdentifierMap.lean.

Each identifier appears exactly once as:
- a ConformanceEvidence field
- an element in `requirements`
Ordering is alphabetical to remove editorial discretion.
-/

/-- Conjunction of a list of propositions. -/
def AndList : List Prop -> Prop
| [] => True
| p :: ps => p ∧ AndList ps

/-
CEE conformance is treated as a structural predicate over evidence.
Interpretation semantics remain external.
-/
structure ConformanceEvidence where
  CEE_ATTESTATION : Prop
  CEE_CONFORMANCE_AE_EP_REQUIRED : Prop
  CEE_CONFORMANCE_SE_REQUIRED : Prop
  CEE_CONTEXT_TAG : Prop
  CEE_DEFINITION_CORE : Prop
  CEE_EXPLANATION_RECORD : Prop
  CEE_MULTIPLICITY : Prop
  CEE_PROVENANCE : Prop
  CEE_SCOPE_EXCLUSIONS : Prop

/-- Alphabetized requirements list for CEE v1. -/
def requirements (e : ConformanceEvidence) : List Prop :=
  [ e.CEE_ATTESTATION
  , e.CEE_CONFORMANCE_AE_EP_REQUIRED
  , e.CEE_CONFORMANCE_SE_REQUIRED
  , e.CEE_CONTEXT_TAG
  , e.CEE_DEFINITION_CORE
  , e.CEE_EXPLANATION_RECORD
  , e.CEE_MULTIPLICITY
  , e.CEE_PROVENANCE
  , e.CEE_SCOPE_EXCLUSIONS
  ]

/-- CEE conformance predicate: all CEE requirements hold. -/
def Conforms (e : ConformanceEvidence) : Prop :=
  AndList (requirements e)

/-- If `AndList ps` holds, then every member of `ps` holds. -/
theorem andList_of_mem {ps : List Prop} {p : Prop} :
    p ∈ ps -> AndList ps -> p := by
  intro hmem hand
  induction ps with
  | nil =>
      cases hmem
  | cons a as ih =>
      have hand' : a ∧ AndList as := by
        simpa [AndList] using hand
      have ha : a := hand'.1
      have hrest : AndList as := hand'.2
      have hmem' : p = a ∨ p ∈ as := by
        simpa using hmem
      cases hmem' with
      | inl hpa =>
          subst hpa
          exact ha
      | inr htail =>
          exact ih htail hrest

/-- Generic extractor: if `p` is listed and `Conforms` holds, then `p` holds. -/
theorem conforms_of_mem (e : ConformanceEvidence) (p : Prop) :
    p ∈ requirements e -> Conforms e -> p := by
  intro hmem hconf
  unfold Conforms at hconf
  exact andList_of_mem (ps := requirements e) (p := p) hmem hconf

end CEE.Conformance
