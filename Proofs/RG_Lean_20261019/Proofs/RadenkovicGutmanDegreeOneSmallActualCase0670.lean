/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0670 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0670 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0670 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0670_checked : acceptsGraphIso
    (source (graph core0670) (root 7) 0 1) SmallGeFourSpectrum043.graph sourceMap0670=true := by decide +kernel
theorem fusedMap0670_checked : acceptsGraphIso
    (fused (graph core0670) (root 7) 0 1) SmallGeFourSpectrum044.graph fusedMap0670=true := by decide +kernel
theorem certified0670 : Certified (graph core0670) (root 7) 0 1 :=
  of_native_maps core0670 SmallGeFourSpectrum043.graph SmallGeFourSpectrum044.graph
    sourceMap0670 fusedMap0670 sourceMap0670_checked fusedMap0670_checked
    DegreeOneSmallComparisons.comparison0670
#print axioms sourceMap0670_checked
#print axioms fusedMap0670_checked
#print axioms certified0670
def sourceMap0670swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0670swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0670swap_checked : acceptsGraphIso
    (source (graph core0670) (root 7) 1 0) SmallGeFourSpectrum043.graph sourceMap0670swap=true := by decide +kernel
theorem fusedMap0670swap_checked : acceptsGraphIso
    (fused (graph core0670) (root 7) 1 0) SmallGeFourSpectrum044.graph fusedMap0670swap=true := by decide +kernel
theorem certified0670swap : Certified (graph core0670) (root 7) 1 0 :=
  of_native_maps core0670 SmallGeFourSpectrum043.graph SmallGeFourSpectrum044.graph
    sourceMap0670swap fusedMap0670swap sourceMap0670swap_checked fusedMap0670swap_checked
    DegreeOneSmallComparisons.comparison0670
#print axioms sourceMap0670swap_checked
#print axioms fusedMap0670swap_checked
#print axioms certified0670swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
