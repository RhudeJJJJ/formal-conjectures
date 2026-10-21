/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0977 : Family 8 := level8.get ⟨85,by decide⟩
def sourceMap0977 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0977 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0977_checked : acceptsGraphIso
    (source (graph core0977) (root 8) 0 2) DegreeOneSmallSpectrum1506.graph sourceMap0977=true := by decide +kernel
theorem fusedMap0977_checked : acceptsGraphIso
    (fused (graph core0977) (root 8) 0 2) DegreeOneSmallSpectrum969.graph fusedMap0977=true := by decide +kernel
theorem certified0977 : Certified (graph core0977) (root 8) 0 2 :=
  of_native_maps core0977 DegreeOneSmallSpectrum1506.graph DegreeOneSmallSpectrum969.graph
    sourceMap0977 fusedMap0977 sourceMap0977_checked fusedMap0977_checked
    DegreeOneSmallComparisons.comparison0977
#print axioms sourceMap0977_checked
#print axioms fusedMap0977_checked
#print axioms certified0977
def sourceMap0977swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0977swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0977swap_checked : acceptsGraphIso
    (source (graph core0977) (root 8) 2 0) DegreeOneSmallSpectrum1506.graph sourceMap0977swap=true := by decide +kernel
theorem fusedMap0977swap_checked : acceptsGraphIso
    (fused (graph core0977) (root 8) 2 0) DegreeOneSmallSpectrum969.graph fusedMap0977swap=true := by decide +kernel
theorem certified0977swap : Certified (graph core0977) (root 8) 2 0 :=
  of_native_maps core0977 DegreeOneSmallSpectrum1506.graph DegreeOneSmallSpectrum969.graph
    sourceMap0977swap fusedMap0977swap sourceMap0977swap_checked fusedMap0977swap_checked
    DegreeOneSmallComparisons.comparison0977
#print axioms sourceMap0977swap_checked
#print axioms fusedMap0977swap_checked
#print axioms certified0977swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
