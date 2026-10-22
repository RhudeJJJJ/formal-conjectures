/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0876 : Family 10 := level10.get ⟨1388,by decide⟩
def sourceMap0876 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0876 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0876_checked : acceptsGraphIso
    (source (graph core0876) (root 10) 0 0) DegreeOneSmallSpectrum1451.graph sourceMap0876=true := by decide +kernel
theorem fusedMap0876_checked : acceptsGraphIso
    (fused (graph core0876) (root 10) 0 0) DegreeOneSmallSpectrum1450.graph fusedMap0876=true := by decide +kernel
theorem certified0876 : Certified (graph core0876) (root 10) 0 0 :=
  of_native_maps core0876 DegreeOneSmallSpectrum1451.graph DegreeOneSmallSpectrum1450.graph
    sourceMap0876 fusedMap0876 sourceMap0876_checked fusedMap0876_checked
    DegreeTwoThreeFiniteComparisons.comparison0876
#print axioms sourceMap0876_checked
#print axioms fusedMap0876_checked
#print axioms certified0876
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
