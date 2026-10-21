/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0642 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0642 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0642 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0642_checked : acceptsGraphIso
    (source (graph core0642) (root 7) 0 3) DegreeOneSmallSpectrum1424.graph sourceMap0642=true := by decide +kernel
theorem fusedMap0642_checked : acceptsGraphIso
    (fused (graph core0642) (root 7) 0 3) DegreeOneSmallSpectrum924.graph fusedMap0642=true := by decide +kernel
theorem certified0642 : Certified (graph core0642) (root 7) 0 3 :=
  of_native_maps core0642 DegreeOneSmallSpectrum1424.graph DegreeOneSmallSpectrum924.graph
    sourceMap0642 fusedMap0642 sourceMap0642_checked fusedMap0642_checked
    DegreeOneSmallComparisons.comparison0642
#print axioms sourceMap0642_checked
#print axioms fusedMap0642_checked
#print axioms certified0642
def sourceMap0642swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0642swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0642swap_checked : acceptsGraphIso
    (source (graph core0642) (root 7) 3 0) DegreeOneSmallSpectrum1424.graph sourceMap0642swap=true := by decide +kernel
theorem fusedMap0642swap_checked : acceptsGraphIso
    (fused (graph core0642) (root 7) 3 0) DegreeOneSmallSpectrum924.graph fusedMap0642swap=true := by decide +kernel
theorem certified0642swap : Certified (graph core0642) (root 7) 3 0 :=
  of_native_maps core0642 DegreeOneSmallSpectrum1424.graph DegreeOneSmallSpectrum924.graph
    sourceMap0642swap fusedMap0642swap sourceMap0642swap_checked fusedMap0642swap_checked
    DegreeOneSmallComparisons.comparison0642
#print axioms sourceMap0642swap_checked
#print axioms fusedMap0642swap_checked
#print axioms certified0642swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
