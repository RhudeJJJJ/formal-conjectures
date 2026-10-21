/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0745 : Family 8 := level8.get ⟨2,by decide⟩
def sourceMap0745 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0745 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0745_checked : acceptsGraphIso
    (source (graph core0745) (root 8) 0 2) DegreeOneSmallSpectrum940.graph sourceMap0745=true := by decide +kernel
theorem fusedMap0745_checked : acceptsGraphIso
    (fused (graph core0745) (root 8) 0 2) DegreeOneSmallSpectrum857.graph fusedMap0745=true := by decide +kernel
theorem certified0745 : Certified (graph core0745) (root 8) 0 2 :=
  of_native_maps core0745 DegreeOneSmallSpectrum940.graph DegreeOneSmallSpectrum857.graph
    sourceMap0745 fusedMap0745 sourceMap0745_checked fusedMap0745_checked
    DegreeOneSmallComparisons.comparison0745
#print axioms sourceMap0745_checked
#print axioms fusedMap0745_checked
#print axioms certified0745
def sourceMap0745swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0745swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0745swap_checked : acceptsGraphIso
    (source (graph core0745) (root 8) 2 0) DegreeOneSmallSpectrum940.graph sourceMap0745swap=true := by decide +kernel
theorem fusedMap0745swap_checked : acceptsGraphIso
    (fused (graph core0745) (root 8) 2 0) DegreeOneSmallSpectrum857.graph fusedMap0745swap=true := by decide +kernel
theorem certified0745swap : Certified (graph core0745) (root 8) 2 0 :=
  of_native_maps core0745 DegreeOneSmallSpectrum940.graph DegreeOneSmallSpectrum857.graph
    sourceMap0745swap fusedMap0745swap sourceMap0745swap_checked fusedMap0745swap_checked
    DegreeOneSmallComparisons.comparison0745
#print axioms sourceMap0745swap_checked
#print axioms fusedMap0745swap_checked
#print axioms certified0745swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
