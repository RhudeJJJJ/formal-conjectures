/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0552 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0552 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0552 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0552_checked : acceptsGraphIso
    (source (graph core0552) (root 7) 0 3) DegreeOneSmallSpectrum970.graph sourceMap0552=true := by decide +kernel
theorem fusedMap0552_checked : acceptsGraphIso
    (fused (graph core0552) (root 7) 0 3) DegreeOneSmallSpectrum971.graph fusedMap0552=true := by decide +kernel
theorem certified0552 : Certified (graph core0552) (root 7) 0 3 :=
  of_native_maps core0552 DegreeOneSmallSpectrum970.graph DegreeOneSmallSpectrum971.graph
    sourceMap0552 fusedMap0552 sourceMap0552_checked fusedMap0552_checked
    DegreeOneSmallComparisons.comparison0552
#print axioms sourceMap0552_checked
#print axioms fusedMap0552_checked
#print axioms certified0552
def sourceMap0552swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0552swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0552swap_checked : acceptsGraphIso
    (source (graph core0552) (root 7) 3 0) DegreeOneSmallSpectrum970.graph sourceMap0552swap=true := by decide +kernel
theorem fusedMap0552swap_checked : acceptsGraphIso
    (fused (graph core0552) (root 7) 3 0) DegreeOneSmallSpectrum971.graph fusedMap0552swap=true := by decide +kernel
theorem certified0552swap : Certified (graph core0552) (root 7) 3 0 :=
  of_native_maps core0552 DegreeOneSmallSpectrum970.graph DegreeOneSmallSpectrum971.graph
    sourceMap0552swap fusedMap0552swap sourceMap0552swap_checked fusedMap0552swap_checked
    DegreeOneSmallComparisons.comparison0552
#print axioms sourceMap0552swap_checked
#print axioms fusedMap0552swap_checked
#print axioms certified0552swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
