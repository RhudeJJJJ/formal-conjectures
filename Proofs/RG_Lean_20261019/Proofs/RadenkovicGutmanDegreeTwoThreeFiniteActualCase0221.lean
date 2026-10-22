/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0221 : Family 9 := level9.get ⟨230,by decide⟩
def sourceMap0221 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0221 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0221_checked : acceptsGraphIso
    (source (graph core0221) (root 9) 0 0) DegreeOneSmallSpectrum667.graph sourceMap0221=true := by decide +kernel
theorem fusedMap0221_checked : acceptsGraphIso
    (fused (graph core0221) (root 9) 0 0) DegreeOneSmallSpectrum538.graph fusedMap0221=true := by decide +kernel
theorem certified0221 : Certified (graph core0221) (root 9) 0 0 :=
  of_native_maps core0221 DegreeOneSmallSpectrum667.graph DegreeOneSmallSpectrum538.graph
    sourceMap0221 fusedMap0221 sourceMap0221_checked fusedMap0221_checked
    DegreeTwoThreeFiniteComparisons.comparison0221
#print axioms sourceMap0221_checked
#print axioms fusedMap0221_checked
#print axioms certified0221
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
