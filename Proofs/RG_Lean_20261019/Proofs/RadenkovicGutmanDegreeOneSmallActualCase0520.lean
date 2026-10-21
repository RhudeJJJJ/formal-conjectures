/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0520 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0520 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0520 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0520_checked : acceptsGraphIso
    (source (graph core0520) (root 7) 0 1) DegreeOneSmallSpectrum210.graph sourceMap0520=true := by decide +kernel
theorem fusedMap0520_checked : acceptsGraphIso
    (fused (graph core0520) (root 7) 0 1) DegreeOneSmallSpectrum212.graph fusedMap0520=true := by decide +kernel
theorem certified0520 : Certified (graph core0520) (root 7) 0 1 :=
  of_native_maps core0520 DegreeOneSmallSpectrum210.graph DegreeOneSmallSpectrum212.graph
    sourceMap0520 fusedMap0520 sourceMap0520_checked fusedMap0520_checked
    DegreeOneSmallComparisons.comparison0520
#print axioms sourceMap0520_checked
#print axioms fusedMap0520_checked
#print axioms certified0520
def sourceMap0520swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0520swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0520swap_checked : acceptsGraphIso
    (source (graph core0520) (root 7) 1 0) DegreeOneSmallSpectrum210.graph sourceMap0520swap=true := by decide +kernel
theorem fusedMap0520swap_checked : acceptsGraphIso
    (fused (graph core0520) (root 7) 1 0) DegreeOneSmallSpectrum212.graph fusedMap0520swap=true := by decide +kernel
theorem certified0520swap : Certified (graph core0520) (root 7) 1 0 :=
  of_native_maps core0520 DegreeOneSmallSpectrum210.graph DegreeOneSmallSpectrum212.graph
    sourceMap0520swap fusedMap0520swap sourceMap0520swap_checked fusedMap0520swap_checked
    DegreeOneSmallComparisons.comparison0520
#print axioms sourceMap0520swap_checked
#print axioms fusedMap0520swap_checked
#print axioms certified0520swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
