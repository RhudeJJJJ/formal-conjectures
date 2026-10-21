/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0608 : Family 7 := level7.get ⟨35,by decide⟩
def sourceMap0608 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0608 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0608_checked : acceptsGraphIso
    (source (graph core0608) (root 7) 1 2) DegreeOneSmallSpectrum1223.graph sourceMap0608=true := by decide +kernel
theorem fusedMap0608_checked : acceptsGraphIso
    (fused (graph core0608) (root 7) 1 2) DegreeOneSmallSpectrum881.graph fusedMap0608=true := by decide +kernel
theorem certified0608 : Certified (graph core0608) (root 7) 1 2 :=
  of_native_maps core0608 DegreeOneSmallSpectrum1223.graph DegreeOneSmallSpectrum881.graph
    sourceMap0608 fusedMap0608 sourceMap0608_checked fusedMap0608_checked
    DegreeOneSmallComparisons.comparison0608
#print axioms sourceMap0608_checked
#print axioms fusedMap0608_checked
#print axioms certified0608
def sourceMap0608swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0608swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0608swap_checked : acceptsGraphIso
    (source (graph core0608) (root 7) 2 1) DegreeOneSmallSpectrum1223.graph sourceMap0608swap=true := by decide +kernel
theorem fusedMap0608swap_checked : acceptsGraphIso
    (fused (graph core0608) (root 7) 2 1) DegreeOneSmallSpectrum881.graph fusedMap0608swap=true := by decide +kernel
theorem certified0608swap : Certified (graph core0608) (root 7) 2 1 :=
  of_native_maps core0608 DegreeOneSmallSpectrum1223.graph DegreeOneSmallSpectrum881.graph
    sourceMap0608swap fusedMap0608swap sourceMap0608swap_checked fusedMap0608swap_checked
    DegreeOneSmallComparisons.comparison0608
#print axioms sourceMap0608swap_checked
#print axioms fusedMap0608swap_checked
#print axioms certified0608swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
