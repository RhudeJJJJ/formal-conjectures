/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0482 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0482 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0482 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0482_checked : acceptsGraphIso
    (source (graph core0482) (root 7) 1 2) DegreeOneSmallSpectrum948.graph sourceMap0482=true := by decide +kernel
theorem fusedMap0482_checked : acceptsGraphIso
    (fused (graph core0482) (root 7) 1 2) DegreeOneSmallSpectrum860.graph fusedMap0482=true := by decide +kernel
theorem certified0482 : Certified (graph core0482) (root 7) 1 2 :=
  of_native_maps core0482 DegreeOneSmallSpectrum948.graph DegreeOneSmallSpectrum860.graph
    sourceMap0482 fusedMap0482 sourceMap0482_checked fusedMap0482_checked
    DegreeOneSmallComparisons.comparison0482
#print axioms sourceMap0482_checked
#print axioms fusedMap0482_checked
#print axioms certified0482
def sourceMap0482swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0482swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0482swap_checked : acceptsGraphIso
    (source (graph core0482) (root 7) 2 1) DegreeOneSmallSpectrum948.graph sourceMap0482swap=true := by decide +kernel
theorem fusedMap0482swap_checked : acceptsGraphIso
    (fused (graph core0482) (root 7) 2 1) DegreeOneSmallSpectrum860.graph fusedMap0482swap=true := by decide +kernel
theorem certified0482swap : Certified (graph core0482) (root 7) 2 1 :=
  of_native_maps core0482 DegreeOneSmallSpectrum948.graph DegreeOneSmallSpectrum860.graph
    sourceMap0482swap fusedMap0482swap sourceMap0482swap_checked fusedMap0482swap_checked
    DegreeOneSmallComparisons.comparison0482
#print axioms sourceMap0482swap_checked
#print axioms fusedMap0482swap_checked
#print axioms certified0482swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
