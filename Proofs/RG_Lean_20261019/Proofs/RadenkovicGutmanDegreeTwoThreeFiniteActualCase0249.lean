/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0249 : Family 9 := level9.get ⟨304,by decide⟩
def sourceMap0249 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0249 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0249_checked : acceptsGraphIso
    (source (graph core0249) (root 9) 0 0) DegreeOneSmallSpectrum581.graph sourceMap0249=true := by decide +kernel
theorem fusedMap0249_checked : acceptsGraphIso
    (fused (graph core0249) (root 9) 0 0) DegreeOneSmallSpectrum575.graph fusedMap0249=true := by decide +kernel
theorem certified0249 : Certified (graph core0249) (root 9) 0 0 :=
  of_native_maps core0249 DegreeOneSmallSpectrum581.graph DegreeOneSmallSpectrum575.graph
    sourceMap0249 fusedMap0249 sourceMap0249_checked fusedMap0249_checked
    DegreeTwoThreeFiniteComparisons.comparison0249
#print axioms sourceMap0249_checked
#print axioms fusedMap0249_checked
#print axioms certified0249
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
