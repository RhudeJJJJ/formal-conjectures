/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0652 : Family 7 := level7.get ⟨51,by decide⟩
def sourceMap0652 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0652 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0652_checked : acceptsGraphIso
    (source (graph core0652) (root 7) 0 1) DegreeOneSmallSpectrum342.graph sourceMap0652=true := by decide +kernel
theorem fusedMap0652_checked : acceptsGraphIso
    (fused (graph core0652) (root 7) 0 1) DegreeOneSmallSpectrum219.graph fusedMap0652=true := by decide +kernel
theorem certified0652 : Certified (graph core0652) (root 7) 0 1 :=
  of_native_maps core0652 DegreeOneSmallSpectrum342.graph DegreeOneSmallSpectrum219.graph
    sourceMap0652 fusedMap0652 sourceMap0652_checked fusedMap0652_checked
    DegreeOneSmallComparisons.comparison0652
#print axioms sourceMap0652_checked
#print axioms fusedMap0652_checked
#print axioms certified0652
def sourceMap0652swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0652swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0652swap_checked : acceptsGraphIso
    (source (graph core0652) (root 7) 1 0) DegreeOneSmallSpectrum342.graph sourceMap0652swap=true := by decide +kernel
theorem fusedMap0652swap_checked : acceptsGraphIso
    (fused (graph core0652) (root 7) 1 0) DegreeOneSmallSpectrum219.graph fusedMap0652swap=true := by decide +kernel
theorem certified0652swap : Certified (graph core0652) (root 7) 1 0 :=
  of_native_maps core0652 DegreeOneSmallSpectrum342.graph DegreeOneSmallSpectrum219.graph
    sourceMap0652swap fusedMap0652swap sourceMap0652swap_checked fusedMap0652swap_checked
    DegreeOneSmallComparisons.comparison0652
#print axioms sourceMap0652swap_checked
#print axioms fusedMap0652swap_checked
#print axioms certified0652swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
