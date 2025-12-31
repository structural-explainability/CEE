namespace CEE.Spec

/-!
# CEE Identifier Map

This file defines the stable CEE requirement identifiers and provides a
traceability mapping to Lean anchors (module + declaration).

Identifiers are the sole normative reference mechanism. Ordering here is
alphabetical to remove editorial discretion.

Each identifier in this list should appear exactly once across:
- SPEC.md
- CONFORMANCE.md
- ConformanceEvidence fields
- requirements list
- this IdentifierMap
-/

/-- Stable requirement identifier type. -/
abbrev ReqId := String

/-- A traceability entry connecting a requirement id to a Lean anchor. -/
structure Entry where
  id : ReqId
  description : String
  leanModule : String
  leanDecl : String
  deriving Repr, BEq, DecidableEq

namespace Req

-- Canonical Identifier List (Alphabetical)

def CEE_ATTESTATION               : ReqId := "CEE.ATTESTATION"
def CEE_CONFORMANCE_AE_EP_REQUIRED : ReqId := "CEE.CONFORMANCE.AE.EP.REQUIRED"
def CEE_CONFORMANCE_SE_REQUIRED    : ReqId := "CEE.CONFORMANCE.SE.REQUIRED"
def CEE_CONTEXT_TAG               : ReqId := "CEE.CONTEXT.TAG"
def CEE_DEFINITION_CORE           : ReqId := "CEE.DEFINITION.CORE"
def CEE_EXPLANATION_RECORD        : ReqId := "CEE.EXPLANATION.RECORD"
def CEE_MULTIPLICITY              : ReqId := "CEE.MULTIPLICITY"
def CEE_PROVENANCE                : ReqId := "CEE.PROVENANCE"
def CEE_SCOPE_EXCLUSIONS          : ReqId := "CEE.SCOPE.EXCLUSIONS"

end Req

/--
Canonical traceability entries (alphabetical by id).

OBS:
- `leanModule`/`leanDecl` are anchors. They may evolve as files move,
  but the identifiers must not be renamed or repurposed.
- Keep the list in strict alphabetical order by `id`.
-/
def entries : List Entry :=
  [
    { id := Req.CEE_ATTESTATION
      description := "Records asserting responsibility for an explanation under a given context."
      leanModule := "CEE.Core.Attestation"
      leanDecl := "Attestation" },

    { id := Req.CEE_CONFORMANCE_AE_EP_REQUIRED
      description := "CEE operates over Accountable Entities (AE) and Evolution Protocol (EP) artifacts."
      leanModule := "CEE"
      leanDecl := "CEE_Conformance_AE_EP_Required" },

    { id := Req.CEE_CONFORMANCE_SE_REQUIRED
      description := "CEE conforms to Structural Explainability (SE) neutrality constraints."
      leanModule := "CEE"
      leanDecl := "CEE_Conformance_SE_Required" },

    { id := Req.CEE_CONTEXT_TAG
      description := "Identifiers for interpretive contexts applied to explanations."
      leanModule := "CEE.Core.ContextTag"
      leanDecl := "ContextTag" },

    { id := Req.CEE_DEFINITION_CORE
      description := "Core definition of CEE as interpretive attachments over substrate history."
      leanModule := "CEE"
      leanDecl := "CEE_Definition_Core" },

    { id := Req.CEE_EXPLANATION_RECORD
      description := "Records associating explanatory content with substrate references."
      leanModule := "CEE.Core.ExplanationRecord"
      leanDecl := "ExplanationRecord" },

    { id := Req.CEE_MULTIPLICITY
      description := "Support for multiple, potentially conflicting interpretations."
      leanModule := "CEE.Core.Multiplicity"
      leanDecl := "Multiplicity" },

    { id := Req.CEE_PROVENANCE
      description := "Records describing how explanatory content was produced."
      leanModule := "CEE.Core.Provenance"
      leanDecl := "ProvenanceRecord" },

    { id := Req.CEE_SCOPE_EXCLUSIONS
      description := "Explicit exclusions: CEE does not modify substrate structure or assert causal/normative conclusions as facts."
      leanModule := "CEE"
      leanDecl := "CEE_Scope_Exclusions" }
  ]

/-- Lookup a traceability entry by identifier. -/
def lookup (rid : ReqId) : Option Entry :=
  entries.find? (fun e => e.id = rid)

end CEE.Spec
