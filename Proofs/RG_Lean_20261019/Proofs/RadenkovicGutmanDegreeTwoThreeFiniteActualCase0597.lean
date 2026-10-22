/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0597 : Family 10 := level10.get ⟨678,by decide⟩
def sourceMap0597 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0597 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0597_checked : acceptsGraphIso
    (source (graph core0597) (root 10) 0 0) DegreeOneSmallSpectrum1018.graph sourceMap0597=true := by decide +kernel
theorem fusedMap0597_checked : acceptsGraphIso
    (fused (graph core0597) (root 10) 0 0) DegreeOneSmallSpectrum1012.graph fusedMap0597=true := by decide +kernel
theorem certified0597 : Certified (graph core0597) (root 10) 0 0 :=
  of_native_maps core0597 DegreeOneSmallSpectrum1018.graph DegreeOneSmallSpectrum1012.graph
    sourceMap0597 fusedMap0597 sourceMap0597_checked fusedMap0597_checked
    DegreeTwoThreeFiniteComparisons.comparison0597
#print axioms sourceMap0597_checked
#print axioms fusedMap0597_checked
#print axioms certified0597
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
