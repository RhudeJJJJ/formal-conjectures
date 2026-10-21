/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0701 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0701 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0701 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0701_checked : acceptsGraphIso
    (source (graph core0701) (root 7) 0 2) DegreeOneSmallSpectrum697.graph sourceMap0701=true := by decide +kernel
theorem fusedMap0701_checked : acceptsGraphIso
    (fused (graph core0701) (root 7) 0 2) DegreeOneSmallSpectrum429.graph fusedMap0701=true := by decide +kernel
theorem certified0701 : Certified (graph core0701) (root 7) 0 2 :=
  of_native_maps core0701 DegreeOneSmallSpectrum697.graph DegreeOneSmallSpectrum429.graph
    sourceMap0701 fusedMap0701 sourceMap0701_checked fusedMap0701_checked
    DegreeOneSmallComparisons.comparison0701
#print axioms sourceMap0701_checked
#print axioms fusedMap0701_checked
#print axioms certified0701
def sourceMap0701swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0701swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0701swap_checked : acceptsGraphIso
    (source (graph core0701) (root 7) 2 0) DegreeOneSmallSpectrum697.graph sourceMap0701swap=true := by decide +kernel
theorem fusedMap0701swap_checked : acceptsGraphIso
    (fused (graph core0701) (root 7) 2 0) DegreeOneSmallSpectrum429.graph fusedMap0701swap=true := by decide +kernel
theorem certified0701swap : Certified (graph core0701) (root 7) 2 0 :=
  of_native_maps core0701 DegreeOneSmallSpectrum697.graph DegreeOneSmallSpectrum429.graph
    sourceMap0701swap fusedMap0701swap sourceMap0701swap_checked fusedMap0701swap_checked
    DegreeOneSmallComparisons.comparison0701
#print axioms sourceMap0701swap_checked
#print axioms fusedMap0701swap_checked
#print axioms certified0701swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
