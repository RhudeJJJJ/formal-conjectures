/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0508 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0508 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0508 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0508_checked : acceptsGraphIso
    (source (graph core0508) (root 7) 0 1) DegreeOneSmallSpectrum200.graph sourceMap0508=true := by decide +kernel
theorem fusedMap0508_checked : acceptsGraphIso
    (fused (graph core0508) (root 7) 0 1) DegreeOneSmallSpectrum202.graph fusedMap0508=true := by decide +kernel
theorem certified0508 : Certified (graph core0508) (root 7) 0 1 :=
  of_native_maps core0508 DegreeOneSmallSpectrum200.graph DegreeOneSmallSpectrum202.graph
    sourceMap0508 fusedMap0508 sourceMap0508_checked fusedMap0508_checked
    DegreeOneSmallComparisons.comparison0508
#print axioms sourceMap0508_checked
#print axioms fusedMap0508_checked
#print axioms certified0508
def sourceMap0508swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0508swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0508swap_checked : acceptsGraphIso
    (source (graph core0508) (root 7) 1 0) DegreeOneSmallSpectrum200.graph sourceMap0508swap=true := by decide +kernel
theorem fusedMap0508swap_checked : acceptsGraphIso
    (fused (graph core0508) (root 7) 1 0) DegreeOneSmallSpectrum202.graph fusedMap0508swap=true := by decide +kernel
theorem certified0508swap : Certified (graph core0508) (root 7) 1 0 :=
  of_native_maps core0508 DegreeOneSmallSpectrum200.graph DegreeOneSmallSpectrum202.graph
    sourceMap0508swap fusedMap0508swap sourceMap0508swap_checked fusedMap0508swap_checked
    DegreeOneSmallComparisons.comparison0508
#print axioms sourceMap0508swap_checked
#print axioms fusedMap0508swap_checked
#print axioms certified0508swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
