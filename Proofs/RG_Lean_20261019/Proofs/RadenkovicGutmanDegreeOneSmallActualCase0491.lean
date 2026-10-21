/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0491 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0491 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0491 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0491_checked : acceptsGraphIso
    (source (graph core0491) (root 7) 0 2) DegreeOneSmallSpectrum456.graph sourceMap0491=true := by decide +kernel
theorem fusedMap0491_checked : acceptsGraphIso
    (fused (graph core0491) (root 7) 0 2) DegreeOneSmallSpectrum371.graph fusedMap0491=true := by decide +kernel
theorem certified0491 : Certified (graph core0491) (root 7) 0 2 :=
  of_native_maps core0491 DegreeOneSmallSpectrum456.graph DegreeOneSmallSpectrum371.graph
    sourceMap0491 fusedMap0491 sourceMap0491_checked fusedMap0491_checked
    DegreeOneSmallComparisons.comparison0491
#print axioms sourceMap0491_checked
#print axioms fusedMap0491_checked
#print axioms certified0491
def sourceMap0491swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0491swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0491swap_checked : acceptsGraphIso
    (source (graph core0491) (root 7) 2 0) DegreeOneSmallSpectrum456.graph sourceMap0491swap=true := by decide +kernel
theorem fusedMap0491swap_checked : acceptsGraphIso
    (fused (graph core0491) (root 7) 2 0) DegreeOneSmallSpectrum371.graph fusedMap0491swap=true := by decide +kernel
theorem certified0491swap : Certified (graph core0491) (root 7) 2 0 :=
  of_native_maps core0491 DegreeOneSmallSpectrum456.graph DegreeOneSmallSpectrum371.graph
    sourceMap0491swap fusedMap0491swap sourceMap0491swap_checked fusedMap0491swap_checked
    DegreeOneSmallComparisons.comparison0491
#print axioms sourceMap0491swap_checked
#print axioms fusedMap0491swap_checked
#print axioms certified0491swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
