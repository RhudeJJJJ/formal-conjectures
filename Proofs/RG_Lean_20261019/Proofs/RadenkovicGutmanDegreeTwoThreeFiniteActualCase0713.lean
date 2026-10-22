/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0713 : Family 10 := level10.get ⟨983,by decide⟩
def sourceMap0713 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0713 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0713_checked : acceptsGraphIso
    (source (graph core0713) (root 10) 0 0) DegreeOneSmallSpectrum1323.graph sourceMap0713=true := by decide +kernel
theorem fusedMap0713_checked : acceptsGraphIso
    (fused (graph core0713) (root 10) 0 0) DegreeOneSmallSpectrum1319.graph fusedMap0713=true := by decide +kernel
theorem certified0713 : Certified (graph core0713) (root 10) 0 0 :=
  of_native_maps core0713 DegreeOneSmallSpectrum1323.graph DegreeOneSmallSpectrum1319.graph
    sourceMap0713 fusedMap0713 sourceMap0713_checked fusedMap0713_checked
    DegreeTwoThreeFiniteComparisons.comparison0713
#print axioms sourceMap0713_checked
#print axioms fusedMap0713_checked
#print axioms certified0713
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
