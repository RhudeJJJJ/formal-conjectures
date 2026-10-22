/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0117 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap0117 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0117 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0117_checked : acceptsGraphIso
    (source (graph core0117) (root 8) 0 0) DegreeOneSmallSpectrum337.graph sourceMap0117=true := by decide +kernel
theorem fusedMap0117_checked : acceptsGraphIso
    (fused (graph core0117) (root 8) 0 0) DegreeOneSmallSpectrum329.graph fusedMap0117=true := by decide +kernel
theorem certified0117 : Certified (graph core0117) (root 8) 0 0 :=
  of_native_maps core0117 DegreeOneSmallSpectrum337.graph DegreeOneSmallSpectrum329.graph
    sourceMap0117 fusedMap0117 sourceMap0117_checked fusedMap0117_checked
    DegreeTwoThreeFiniteComparisons.comparison0117
#print axioms sourceMap0117_checked
#print axioms fusedMap0117_checked
#print axioms certified0117
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
