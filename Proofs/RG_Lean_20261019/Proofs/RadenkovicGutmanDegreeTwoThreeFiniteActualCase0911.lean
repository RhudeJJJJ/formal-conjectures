/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0911 : Family 10 := level10.get ⟨1468,by decide⟩
def sourceMap0911 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0911 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0911_checked : acceptsGraphIso
    (source (graph core0911) (root 10) 0 0) DegreeOneSmallSpectrum1422.graph sourceMap0911=true := by decide +kernel
theorem fusedMap0911_checked : acceptsGraphIso
    (fused (graph core0911) (root 10) 0 0) DegreeOneSmallSpectrum1412.graph fusedMap0911=true := by decide +kernel
theorem certified0911 : Certified (graph core0911) (root 10) 0 0 :=
  of_native_maps core0911 DegreeOneSmallSpectrum1422.graph DegreeOneSmallSpectrum1412.graph
    sourceMap0911 fusedMap0911 sourceMap0911_checked fusedMap0911_checked
    DegreeTwoThreeFiniteComparisons.comparison0911
#print axioms sourceMap0911_checked
#print axioms fusedMap0911_checked
#print axioms certified0911
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
