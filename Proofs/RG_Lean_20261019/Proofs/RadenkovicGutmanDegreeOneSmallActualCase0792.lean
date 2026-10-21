/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0792 : Family 8 := level8.get ⟨16,by decide⟩
def sourceMap0792 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0792 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0792_checked : acceptsGraphIso
    (source (graph core0792) (root 8) 0 1) DegreeOneSmallSpectrum546.graph sourceMap0792=true := by decide +kernel
theorem fusedMap0792_checked : acceptsGraphIso
    (fused (graph core0792) (root 8) 0 1) DegreeOneSmallSpectrum381.graph fusedMap0792=true := by decide +kernel
theorem certified0792 : Certified (graph core0792) (root 8) 0 1 :=
  of_native_maps core0792 DegreeOneSmallSpectrum546.graph DegreeOneSmallSpectrum381.graph
    sourceMap0792 fusedMap0792 sourceMap0792_checked fusedMap0792_checked
    DegreeOneSmallComparisons.comparison0792
#print axioms sourceMap0792_checked
#print axioms fusedMap0792_checked
#print axioms certified0792
def sourceMap0792swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0792swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0792swap_checked : acceptsGraphIso
    (source (graph core0792) (root 8) 1 0) DegreeOneSmallSpectrum546.graph sourceMap0792swap=true := by decide +kernel
theorem fusedMap0792swap_checked : acceptsGraphIso
    (fused (graph core0792) (root 8) 1 0) DegreeOneSmallSpectrum381.graph fusedMap0792swap=true := by decide +kernel
theorem certified0792swap : Certified (graph core0792) (root 8) 1 0 :=
  of_native_maps core0792 DegreeOneSmallSpectrum546.graph DegreeOneSmallSpectrum381.graph
    sourceMap0792swap fusedMap0792swap sourceMap0792swap_checked fusedMap0792swap_checked
    DegreeOneSmallComparisons.comparison0792
#print axioms sourceMap0792swap_checked
#print axioms fusedMap0792swap_checked
#print axioms certified0792swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
