/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0916 : Family 8 := level8.get ⟨61,by decide⟩
def sourceMap0916 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0916 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0916_checked : acceptsGraphIso
    (source (graph core0916) (root 8) 0 1) DegreeOneSmallSpectrum538.graph sourceMap0916=true := by decide +kernel
theorem fusedMap0916_checked : acceptsGraphIso
    (fused (graph core0916) (root 8) 0 1) DegreeOneSmallSpectrum540.graph fusedMap0916=true := by decide +kernel
theorem certified0916 : Certified (graph core0916) (root 8) 0 1 :=
  of_native_maps core0916 DegreeOneSmallSpectrum538.graph DegreeOneSmallSpectrum540.graph
    sourceMap0916 fusedMap0916 sourceMap0916_checked fusedMap0916_checked
    DegreeOneSmallComparisons.comparison0916
#print axioms sourceMap0916_checked
#print axioms fusedMap0916_checked
#print axioms certified0916
def sourceMap0916swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0916swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0916swap_checked : acceptsGraphIso
    (source (graph core0916) (root 8) 1 0) DegreeOneSmallSpectrum538.graph sourceMap0916swap=true := by decide +kernel
theorem fusedMap0916swap_checked : acceptsGraphIso
    (fused (graph core0916) (root 8) 1 0) DegreeOneSmallSpectrum540.graph fusedMap0916swap=true := by decide +kernel
theorem certified0916swap : Certified (graph core0916) (root 8) 1 0 :=
  of_native_maps core0916 DegreeOneSmallSpectrum538.graph DegreeOneSmallSpectrum540.graph
    sourceMap0916swap fusedMap0916swap sourceMap0916swap_checked fusedMap0916swap_checked
    DegreeOneSmallComparisons.comparison0916
#print axioms sourceMap0916swap_checked
#print axioms fusedMap0916swap_checked
#print axioms certified0916swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
