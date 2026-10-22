/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0288 : Family 9 := level9.get ⟨406,by decide⟩
def sourceMap0288 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0288 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0288_checked : acceptsGraphIso
    (source (graph core0288) (root 9) 0 0) DegreeOneSmallSpectrum499.graph sourceMap0288=true := by decide +kernel
theorem fusedMap0288_checked : acceptsGraphIso
    (fused (graph core0288) (root 9) 0 0) DegreeOneSmallSpectrum498.graph fusedMap0288=true := by decide +kernel
theorem certified0288 : Certified (graph core0288) (root 9) 0 0 :=
  of_native_maps core0288 DegreeOneSmallSpectrum499.graph DegreeOneSmallSpectrum498.graph
    sourceMap0288 fusedMap0288 sourceMap0288_checked fusedMap0288_checked
    DegreeTwoThreeFiniteComparisons.comparison0288
#print axioms sourceMap0288_checked
#print axioms fusedMap0288_checked
#print axioms certified0288
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
