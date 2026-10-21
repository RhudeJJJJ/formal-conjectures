/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0837 : Family 8 := level8.get ⟨30,by decide⟩
def sourceMap0837 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0837 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 8 0 2 v)
theorem sourceMap0837_checked : acceptsGraphIso
    (source (graph core0837) (root 8) 0 2) DegreeOneSmallSpectrum958.graph sourceMap0837=true := by decide +kernel
theorem fusedMap0837_checked : acceptsGraphIso
    (fused (graph core0837) (root 8) 0 2) DegreeOneSmallSpectrum978.graph fusedMap0837=true := by decide +kernel
theorem certified0837 : Certified (graph core0837) (root 8) 0 2 :=
  of_native_maps core0837 DegreeOneSmallSpectrum958.graph DegreeOneSmallSpectrum978.graph
    sourceMap0837 fusedMap0837 sourceMap0837_checked fusedMap0837_checked
    DegreeOneSmallComparisons.comparison0837
#print axioms sourceMap0837_checked
#print axioms fusedMap0837_checked
#print axioms certified0837
def sourceMap0837swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0837swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 8 2 0 v)
theorem sourceMap0837swap_checked : acceptsGraphIso
    (source (graph core0837) (root 8) 2 0) DegreeOneSmallSpectrum958.graph sourceMap0837swap=true := by decide +kernel
theorem fusedMap0837swap_checked : acceptsGraphIso
    (fused (graph core0837) (root 8) 2 0) DegreeOneSmallSpectrum978.graph fusedMap0837swap=true := by decide +kernel
theorem certified0837swap : Certified (graph core0837) (root 8) 2 0 :=
  of_native_maps core0837 DegreeOneSmallSpectrum958.graph DegreeOneSmallSpectrum978.graph
    sourceMap0837swap fusedMap0837swap sourceMap0837swap_checked fusedMap0837swap_checked
    DegreeOneSmallComparisons.comparison0837
#print axioms sourceMap0837swap_checked
#print axioms fusedMap0837swap_checked
#print axioms certified0837swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
