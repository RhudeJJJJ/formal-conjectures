/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0908 : Family 8 := level8.get ⟨58,by decide⟩
def sourceMap0908 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0908 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0908_checked : acceptsGraphIso
    (source (graph core0908) (root 8) 0 1) DegreeOneSmallSpectrum526.graph sourceMap0908=true := by decide +kernel
theorem fusedMap0908_checked : acceptsGraphIso
    (fused (graph core0908) (root 8) 0 1) DegreeOneSmallSpectrum528.graph fusedMap0908=true := by decide +kernel
theorem certified0908 : Certified (graph core0908) (root 8) 0 1 :=
  of_native_maps core0908 DegreeOneSmallSpectrum526.graph DegreeOneSmallSpectrum528.graph
    sourceMap0908 fusedMap0908 sourceMap0908_checked fusedMap0908_checked
    DegreeOneSmallComparisons.comparison0908
#print axioms sourceMap0908_checked
#print axioms fusedMap0908_checked
#print axioms certified0908
def sourceMap0908swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0908swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0908swap_checked : acceptsGraphIso
    (source (graph core0908) (root 8) 1 0) DegreeOneSmallSpectrum526.graph sourceMap0908swap=true := by decide +kernel
theorem fusedMap0908swap_checked : acceptsGraphIso
    (fused (graph core0908) (root 8) 1 0) DegreeOneSmallSpectrum528.graph fusedMap0908swap=true := by decide +kernel
theorem certified0908swap : Certified (graph core0908) (root 8) 1 0 :=
  of_native_maps core0908 DegreeOneSmallSpectrum526.graph DegreeOneSmallSpectrum528.graph
    sourceMap0908swap fusedMap0908swap sourceMap0908swap_checked fusedMap0908swap_checked
    DegreeOneSmallComparisons.comparison0908
#print axioms sourceMap0908swap_checked
#print axioms fusedMap0908swap_checked
#print axioms certified0908swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
