/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1628 : Family 9 := level9.get ⟨369,by decide⟩
def sourceMap1628 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1628 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1628_checked : acceptsGraphIso
    (source (graph core1628) (root 9) 0 1) DegreeOneSmallSpectrum1805.graph sourceMap1628=true := by decide +kernel
theorem fusedMap1628_checked : acceptsGraphIso
    (fused (graph core1628) (root 9) 0 1) DegreeOneSmallSpectrum1119.graph fusedMap1628=true := by decide +kernel
theorem certified1628 : Certified (graph core1628) (root 9) 0 1 :=
  of_native_maps core1628 DegreeOneSmallSpectrum1805.graph DegreeOneSmallSpectrum1119.graph
    sourceMap1628 fusedMap1628 sourceMap1628_checked fusedMap1628_checked
    DegreeOneSmallComparisons.comparison1628
#print axioms sourceMap1628_checked
#print axioms fusedMap1628_checked
#print axioms certified1628
def sourceMap1628swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1628swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1628swap_checked : acceptsGraphIso
    (source (graph core1628) (root 9) 1 0) DegreeOneSmallSpectrum1805.graph sourceMap1628swap=true := by decide +kernel
theorem fusedMap1628swap_checked : acceptsGraphIso
    (fused (graph core1628) (root 9) 1 0) DegreeOneSmallSpectrum1119.graph fusedMap1628swap=true := by decide +kernel
theorem certified1628swap : Certified (graph core1628) (root 9) 1 0 :=
  of_native_maps core1628 DegreeOneSmallSpectrum1805.graph DegreeOneSmallSpectrum1119.graph
    sourceMap1628swap fusedMap1628swap sourceMap1628swap_checked fusedMap1628swap_checked
    DegreeOneSmallComparisons.comparison1628
#print axioms sourceMap1628swap_checked
#print axioms fusedMap1628swap_checked
#print axioms certified1628swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
