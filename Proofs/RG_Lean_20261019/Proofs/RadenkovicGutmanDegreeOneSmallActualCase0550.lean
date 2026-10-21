/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0550 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0550 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0550 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (fusedLabel 7 0 1 v)
theorem sourceMap0550_checked : acceptsGraphIso
    (source (graph core0550) (root 7) 0 1) DegreeOneSmallSpectrum208.graph sourceMap0550=true := by decide +kernel
theorem fusedMap0550_checked : acceptsGraphIso
    (fused (graph core0550) (root 7) 0 1) DegreeOneSmallSpectrum228.graph fusedMap0550=true := by decide +kernel
theorem certified0550 : Certified (graph core0550) (root 7) 0 1 :=
  of_native_maps core0550 DegreeOneSmallSpectrum208.graph DegreeOneSmallSpectrum228.graph
    sourceMap0550 fusedMap0550 sourceMap0550_checked fusedMap0550_checked
    DegreeOneSmallComparisons.comparison0550
#print axioms sourceMap0550_checked
#print axioms fusedMap0550_checked
#print axioms certified0550
def sourceMap0550swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0550swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (fusedLabel 7 1 0 v)
theorem sourceMap0550swap_checked : acceptsGraphIso
    (source (graph core0550) (root 7) 1 0) DegreeOneSmallSpectrum208.graph sourceMap0550swap=true := by decide +kernel
theorem fusedMap0550swap_checked : acceptsGraphIso
    (fused (graph core0550) (root 7) 1 0) DegreeOneSmallSpectrum228.graph fusedMap0550swap=true := by decide +kernel
theorem certified0550swap : Certified (graph core0550) (root 7) 1 0 :=
  of_native_maps core0550 DegreeOneSmallSpectrum208.graph DegreeOneSmallSpectrum228.graph
    sourceMap0550swap fusedMap0550swap sourceMap0550swap_checked fusedMap0550swap_checked
    DegreeOneSmallComparisons.comparison0550
#print axioms sourceMap0550swap_checked
#print axioms fusedMap0550swap_checked
#print axioms certified0550swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
