/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1572 : Family 9 := level9.get ⟨317,by decide⟩
def sourceMap1572 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1572 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1572_checked : acceptsGraphIso
    (source (graph core1572) (root 9) 0 1) DegreeOneSmallSpectrum1530.graph sourceMap1572=true := by decide +kernel
theorem fusedMap1572_checked : acceptsGraphIso
    (fused (graph core1572) (root 9) 0 1) DegreeOneSmallSpectrum979.graph fusedMap1572=true := by decide +kernel
theorem certified1572 : Certified (graph core1572) (root 9) 0 1 :=
  of_native_maps core1572 DegreeOneSmallSpectrum1530.graph DegreeOneSmallSpectrum979.graph
    sourceMap1572 fusedMap1572 sourceMap1572_checked fusedMap1572_checked
    DegreeOneSmallComparisons.comparison1572
#print axioms sourceMap1572_checked
#print axioms fusedMap1572_checked
#print axioms certified1572
def sourceMap1572swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1572swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1572swap_checked : acceptsGraphIso
    (source (graph core1572) (root 9) 1 0) DegreeOneSmallSpectrum1530.graph sourceMap1572swap=true := by decide +kernel
theorem fusedMap1572swap_checked : acceptsGraphIso
    (fused (graph core1572) (root 9) 1 0) DegreeOneSmallSpectrum979.graph fusedMap1572swap=true := by decide +kernel
theorem certified1572swap : Certified (graph core1572) (root 9) 1 0 :=
  of_native_maps core1572 DegreeOneSmallSpectrum1530.graph DegreeOneSmallSpectrum979.graph
    sourceMap1572swap fusedMap1572swap sourceMap1572swap_checked fusedMap1572swap_checked
    DegreeOneSmallComparisons.comparison1572
#print axioms sourceMap1572swap_checked
#print axioms fusedMap1572swap_checked
#print axioms certified1572swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
