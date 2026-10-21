/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0466 : Family 7 := level7.get ⟨3,by decide⟩
def sourceMap0466 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 7 0 1 v)
def fusedMap0466 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0466_checked : acceptsGraphIso
    (source (graph core0466) (root 7) 0 1) DegreeOneSmallSpectrum216.graph sourceMap0466=true := by decide +kernel
theorem fusedMap0466_checked : acceptsGraphIso
    (fused (graph core0466) (root 7) 0 1) DegreeOneSmallSpectrum166.graph fusedMap0466=true := by decide +kernel
theorem certified0466 : Certified (graph core0466) (root 7) 0 1 :=
  of_native_maps core0466 DegreeOneSmallSpectrum216.graph DegreeOneSmallSpectrum166.graph
    sourceMap0466 fusedMap0466 sourceMap0466_checked fusedMap0466_checked
    DegreeOneSmallComparisons.comparison0466
#print axioms sourceMap0466_checked
#print axioms fusedMap0466_checked
#print axioms certified0466
def sourceMap0466swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 7 1 0 v)
def fusedMap0466swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0466swap_checked : acceptsGraphIso
    (source (graph core0466) (root 7) 1 0) DegreeOneSmallSpectrum216.graph sourceMap0466swap=true := by decide +kernel
theorem fusedMap0466swap_checked : acceptsGraphIso
    (fused (graph core0466) (root 7) 1 0) DegreeOneSmallSpectrum166.graph fusedMap0466swap=true := by decide +kernel
theorem certified0466swap : Certified (graph core0466) (root 7) 1 0 :=
  of_native_maps core0466 DegreeOneSmallSpectrum216.graph DegreeOneSmallSpectrum166.graph
    sourceMap0466swap fusedMap0466swap sourceMap0466swap_checked fusedMap0466swap_checked
    DegreeOneSmallComparisons.comparison0466
#print axioms sourceMap0466swap_checked
#print axioms fusedMap0466swap_checked
#print axioms certified0466swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
