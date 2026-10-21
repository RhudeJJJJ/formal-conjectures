/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1596 : Family 9 := level9.get ⟨335,by decide⟩
def sourceMap1596 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1596 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1596_checked : acceptsGraphIso
    (source (graph core1596) (root 9) 0 1) DegreeOneSmallSpectrum1652.graph sourceMap1596=true := by decide +kernel
theorem fusedMap1596_checked : acceptsGraphIso
    (fused (graph core1596) (root 9) 0 1) DegreeOneSmallSpectrum1017.graph fusedMap1596=true := by decide +kernel
theorem certified1596 : Certified (graph core1596) (root 9) 0 1 :=
  of_native_maps core1596 DegreeOneSmallSpectrum1652.graph DegreeOneSmallSpectrum1017.graph
    sourceMap1596 fusedMap1596 sourceMap1596_checked fusedMap1596_checked
    DegreeOneSmallComparisons.comparison1596
#print axioms sourceMap1596_checked
#print axioms fusedMap1596_checked
#print axioms certified1596
def sourceMap1596swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1596swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1596swap_checked : acceptsGraphIso
    (source (graph core1596) (root 9) 1 0) DegreeOneSmallSpectrum1652.graph sourceMap1596swap=true := by decide +kernel
theorem fusedMap1596swap_checked : acceptsGraphIso
    (fused (graph core1596) (root 9) 1 0) DegreeOneSmallSpectrum1017.graph fusedMap1596swap=true := by decide +kernel
theorem certified1596swap : Certified (graph core1596) (root 9) 1 0 :=
  of_native_maps core1596 DegreeOneSmallSpectrum1652.graph DegreeOneSmallSpectrum1017.graph
    sourceMap1596swap fusedMap1596swap sourceMap1596swap_checked fusedMap1596swap_checked
    DegreeOneSmallComparisons.comparison1596
#print axioms sourceMap1596swap_checked
#print axioms fusedMap1596swap_checked
#print axioms certified1596swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
