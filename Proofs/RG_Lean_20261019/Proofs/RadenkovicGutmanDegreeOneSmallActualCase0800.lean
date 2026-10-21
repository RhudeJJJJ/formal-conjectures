/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0800 : Family 8 := level8.get ⟨18,by decide⟩
def sourceMap0800 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0800 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0800_checked : acceptsGraphIso
    (source (graph core0800) (root 8) 0 1) DegreeOneSmallSpectrum546.graph sourceMap0800=true := by decide +kernel
theorem fusedMap0800_checked : acceptsGraphIso
    (fused (graph core0800) (root 8) 0 1) DegreeOneSmallSpectrum385.graph fusedMap0800=true := by decide +kernel
theorem certified0800 : Certified (graph core0800) (root 8) 0 1 :=
  of_native_maps core0800 DegreeOneSmallSpectrum546.graph DegreeOneSmallSpectrum385.graph
    sourceMap0800 fusedMap0800 sourceMap0800_checked fusedMap0800_checked
    DegreeOneSmallComparisons.comparison0800
#print axioms sourceMap0800_checked
#print axioms fusedMap0800_checked
#print axioms certified0800
def sourceMap0800swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0800swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0800swap_checked : acceptsGraphIso
    (source (graph core0800) (root 8) 1 0) DegreeOneSmallSpectrum546.graph sourceMap0800swap=true := by decide +kernel
theorem fusedMap0800swap_checked : acceptsGraphIso
    (fused (graph core0800) (root 8) 1 0) DegreeOneSmallSpectrum385.graph fusedMap0800swap=true := by decide +kernel
theorem certified0800swap : Certified (graph core0800) (root 8) 1 0 :=
  of_native_maps core0800 DegreeOneSmallSpectrum546.graph DegreeOneSmallSpectrum385.graph
    sourceMap0800swap fusedMap0800swap sourceMap0800swap_checked fusedMap0800swap_checked
    DegreeOneSmallComparisons.comparison0800
#print axioms sourceMap0800swap_checked
#print axioms fusedMap0800swap_checked
#print axioms certified0800swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
