/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0654 : Family 10 := level10.get ⟨846,by decide⟩
def sourceMap0654 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0654 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0654_checked : acceptsGraphIso
    (source (graph core0654) (root 10) 0 0) DegreeOneSmallSpectrum1693.graph sourceMap0654=true := by decide +kernel
theorem fusedMap0654_checked : acceptsGraphIso
    (fused (graph core0654) (root 10) 0 0) DegreeOneSmallSpectrum1441.graph fusedMap0654=true := by decide +kernel
theorem certified0654 : Certified (graph core0654) (root 10) 0 0 :=
  of_native_maps core0654 DegreeOneSmallSpectrum1693.graph DegreeOneSmallSpectrum1441.graph
    sourceMap0654 fusedMap0654 sourceMap0654_checked fusedMap0654_checked
    DegreeTwoThreeFiniteComparisons.comparison0654
#print axioms sourceMap0654_checked
#print axioms fusedMap0654_checked
#print axioms certified0654
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
