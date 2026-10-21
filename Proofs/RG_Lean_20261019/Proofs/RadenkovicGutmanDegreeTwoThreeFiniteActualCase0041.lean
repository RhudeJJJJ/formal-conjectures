/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0041 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap0041 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,5,6,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0041 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0041_checked : acceptsGraphIso
    (source (graph core0041) (root 7) 0 0) DegreeOneSmallSpectrum097.graph sourceMap0041=true := by decide +kernel
theorem fusedMap0041_checked : acceptsGraphIso
    (fused (graph core0041) (root 7) 0 0) DegreeOneSmallSpectrum144.graph fusedMap0041=true := by decide +kernel
theorem certified0041 : Certified (graph core0041) (root 7) 0 0 :=
  of_native_maps core0041 DegreeOneSmallSpectrum097.graph DegreeOneSmallSpectrum144.graph
    sourceMap0041 fusedMap0041 sourceMap0041_checked fusedMap0041_checked
    DegreeTwoThreeFiniteComparisons.comparison0041
#print axioms sourceMap0041_checked
#print axioms fusedMap0041_checked
#print axioms certified0041
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
