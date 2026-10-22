/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0681 : Family 10 := level10.get ⟨913,by decide⟩
def sourceMap0681 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0681 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0681_checked : acceptsGraphIso
    (source (graph core0681) (root 10) 0 0) DegreeOneSmallSpectrum1123.graph sourceMap0681=true := by decide +kernel
theorem fusedMap0681_checked : acceptsGraphIso
    (fused (graph core0681) (root 10) 0 0) DegreeOneSmallSpectrum1100.graph fusedMap0681=true := by decide +kernel
theorem certified0681 : Certified (graph core0681) (root 10) 0 0 :=
  of_native_maps core0681 DegreeOneSmallSpectrum1123.graph DegreeOneSmallSpectrum1100.graph
    sourceMap0681 fusedMap0681 sourceMap0681_checked fusedMap0681_checked
    DegreeTwoThreeFiniteComparisons.comparison0681
#print axioms sourceMap0681_checked
#print axioms fusedMap0681_checked
#print axioms certified0681
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
