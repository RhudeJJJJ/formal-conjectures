/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0496 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0496 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0496 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0496_checked : acceptsGraphIso
    (source (graph core0496) (root 7) 0 1) DegreeOneSmallSpectrum186.graph sourceMap0496=true := by decide +kernel
theorem fusedMap0496_checked : acceptsGraphIso
    (fused (graph core0496) (root 7) 0 1) DegreeOneSmallSpectrum188.graph fusedMap0496=true := by decide +kernel
theorem certified0496 : Certified (graph core0496) (root 7) 0 1 :=
  of_native_maps core0496 DegreeOneSmallSpectrum186.graph DegreeOneSmallSpectrum188.graph
    sourceMap0496 fusedMap0496 sourceMap0496_checked fusedMap0496_checked
    DegreeOneSmallComparisons.comparison0496
#print axioms sourceMap0496_checked
#print axioms fusedMap0496_checked
#print axioms certified0496
def sourceMap0496swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0496swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0496swap_checked : acceptsGraphIso
    (source (graph core0496) (root 7) 1 0) DegreeOneSmallSpectrum186.graph sourceMap0496swap=true := by decide +kernel
theorem fusedMap0496swap_checked : acceptsGraphIso
    (fused (graph core0496) (root 7) 1 0) DegreeOneSmallSpectrum188.graph fusedMap0496swap=true := by decide +kernel
theorem certified0496swap : Certified (graph core0496) (root 7) 1 0 :=
  of_native_maps core0496 DegreeOneSmallSpectrum186.graph DegreeOneSmallSpectrum188.graph
    sourceMap0496swap fusedMap0496swap sourceMap0496swap_checked fusedMap0496swap_checked
    DegreeOneSmallComparisons.comparison0496
#print axioms sourceMap0496swap_checked
#print axioms fusedMap0496swap_checked
#print axioms certified0496swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
