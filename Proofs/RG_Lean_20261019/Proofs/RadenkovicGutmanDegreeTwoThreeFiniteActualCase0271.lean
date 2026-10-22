/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0271 : Family 9 := level9.get ⟨364,by decide⟩
def sourceMap0271 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0271 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0271_checked : acceptsGraphIso
    (source (graph core0271) (root 9) 0 0) DegreeOneSmallSpectrum705.graph sourceMap0271=true := by decide +kernel
theorem fusedMap0271_checked : acceptsGraphIso
    (fused (graph core0271) (root 9) 0 0) DegreeOneSmallSpectrum703.graph fusedMap0271=true := by decide +kernel
theorem certified0271 : Certified (graph core0271) (root 9) 0 0 :=
  of_native_maps core0271 DegreeOneSmallSpectrum705.graph DegreeOneSmallSpectrum703.graph
    sourceMap0271 fusedMap0271 sourceMap0271_checked fusedMap0271_checked
    DegreeTwoThreeFiniteComparisons.comparison0271
#print axioms sourceMap0271_checked
#print axioms fusedMap0271_checked
#print axioms certified0271
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
