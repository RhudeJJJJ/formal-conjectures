/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0216 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0216 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0216 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0216_checked : acceptsGraphIso
    (source (graph core0216) (root 5) 1 4) DegreeOneSmallSpectrum1044.graph sourceMap0216=true := by decide +kernel
theorem fusedMap0216_checked : acceptsGraphIso
    (fused (graph core0216) (root 5) 1 4) DegreeOneSmallSpectrum870.graph fusedMap0216=true := by decide +kernel
theorem certified0216 : Certified (graph core0216) (root 5) 1 4 :=
  of_native_maps core0216 DegreeOneSmallSpectrum1044.graph DegreeOneSmallSpectrum870.graph
    sourceMap0216 fusedMap0216 sourceMap0216_checked fusedMap0216_checked
    DegreeOneSmallComparisons.comparison0216
#print axioms sourceMap0216_checked
#print axioms fusedMap0216_checked
#print axioms certified0216
def sourceMap0216swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap0216swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0216swap_checked : acceptsGraphIso
    (source (graph core0216) (root 5) 4 1) DegreeOneSmallSpectrum1044.graph sourceMap0216swap=true := by decide +kernel
theorem fusedMap0216swap_checked : acceptsGraphIso
    (fused (graph core0216) (root 5) 4 1) DegreeOneSmallSpectrum870.graph fusedMap0216swap=true := by decide +kernel
theorem certified0216swap : Certified (graph core0216) (root 5) 4 1 :=
  of_native_maps core0216 DegreeOneSmallSpectrum1044.graph DegreeOneSmallSpectrum870.graph
    sourceMap0216swap fusedMap0216swap sourceMap0216swap_checked fusedMap0216swap_checked
    DegreeOneSmallComparisons.comparison0216
#print axioms sourceMap0216swap_checked
#print axioms fusedMap0216swap_checked
#print axioms certified0216swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
