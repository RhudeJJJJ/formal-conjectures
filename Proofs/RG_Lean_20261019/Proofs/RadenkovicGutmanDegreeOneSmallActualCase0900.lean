/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0900 : Family 8 := level8.get ⟨55,by decide⟩
def sourceMap0900 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap0900 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0900_checked : acceptsGraphIso
    (source (graph core0900) (root 8) 0 1) DegreeOneSmallSpectrum513.graph sourceMap0900=true := by decide +kernel
theorem fusedMap0900_checked : acceptsGraphIso
    (fused (graph core0900) (root 8) 0 1) DegreeOneSmallSpectrum518.graph fusedMap0900=true := by decide +kernel
theorem certified0900 : Certified (graph core0900) (root 8) 0 1 :=
  of_native_maps core0900 DegreeOneSmallSpectrum513.graph DegreeOneSmallSpectrum518.graph
    sourceMap0900 fusedMap0900 sourceMap0900_checked fusedMap0900_checked
    DegreeOneSmallComparisons.comparison0900
#print axioms sourceMap0900_checked
#print axioms fusedMap0900_checked
#print axioms certified0900
def sourceMap0900swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap0900swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0900swap_checked : acceptsGraphIso
    (source (graph core0900) (root 8) 1 0) DegreeOneSmallSpectrum513.graph sourceMap0900swap=true := by decide +kernel
theorem fusedMap0900swap_checked : acceptsGraphIso
    (fused (graph core0900) (root 8) 1 0) DegreeOneSmallSpectrum518.graph fusedMap0900swap=true := by decide +kernel
theorem certified0900swap : Certified (graph core0900) (root 8) 1 0 :=
  of_native_maps core0900 DegreeOneSmallSpectrum513.graph DegreeOneSmallSpectrum518.graph
    sourceMap0900swap fusedMap0900swap sourceMap0900swap_checked fusedMap0900swap_checked
    DegreeOneSmallComparisons.comparison0900
#print axioms sourceMap0900swap_checked
#print axioms fusedMap0900swap_checked
#print axioms certified0900swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
