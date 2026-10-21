/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0816 : Family 8 := level8.get ⟨23,by decide⟩
def sourceMap0816 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0816 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0816_checked : acceptsGraphIso
    (source (graph core0816) (root 8) 0 1) DegreeOneSmallSpectrum549.graph sourceMap0816=true := by decide +kernel
theorem fusedMap0816_checked : acceptsGraphIso
    (fused (graph core0816) (root 8) 0 1) DegreeOneSmallSpectrum391.graph fusedMap0816=true := by decide +kernel
theorem certified0816 : Certified (graph core0816) (root 8) 0 1 :=
  of_native_maps core0816 DegreeOneSmallSpectrum549.graph DegreeOneSmallSpectrum391.graph
    sourceMap0816 fusedMap0816 sourceMap0816_checked fusedMap0816_checked
    DegreeOneSmallComparisons.comparison0816
#print axioms sourceMap0816_checked
#print axioms fusedMap0816_checked
#print axioms certified0816
def sourceMap0816swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0816swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0816swap_checked : acceptsGraphIso
    (source (graph core0816) (root 8) 1 0) DegreeOneSmallSpectrum549.graph sourceMap0816swap=true := by decide +kernel
theorem fusedMap0816swap_checked : acceptsGraphIso
    (fused (graph core0816) (root 8) 1 0) DegreeOneSmallSpectrum391.graph fusedMap0816swap=true := by decide +kernel
theorem certified0816swap : Certified (graph core0816) (root 8) 1 0 :=
  of_native_maps core0816 DegreeOneSmallSpectrum549.graph DegreeOneSmallSpectrum391.graph
    sourceMap0816swap fusedMap0816swap sourceMap0816swap_checked fusedMap0816swap_checked
    DegreeOneSmallComparisons.comparison0816
#print axioms sourceMap0816swap_checked
#print axioms fusedMap0816swap_checked
#print axioms certified0816swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
