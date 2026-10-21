/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1562 : Family 9 := level9.get ⟨292,by decide⟩
def sourceMap1562 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1562 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1562_checked : acceptsGraphIso
    (source (graph core1562) (root 9) 0 1) DegreeOneSmallSpectrum1399.graph sourceMap1562=true := by decide +kernel
theorem fusedMap1562_checked : acceptsGraphIso
    (fused (graph core1562) (root 9) 0 1) DegreeOneSmallSpectrum1512.graph fusedMap1562=true := by decide +kernel
theorem certified1562 : Certified (graph core1562) (root 9) 0 1 :=
  of_native_maps core1562 DegreeOneSmallSpectrum1399.graph DegreeOneSmallSpectrum1512.graph
    sourceMap1562 fusedMap1562 sourceMap1562_checked fusedMap1562_checked
    DegreeOneSmallComparisons.comparison1562
#print axioms sourceMap1562_checked
#print axioms fusedMap1562_checked
#print axioms certified1562
def sourceMap1562swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1562swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1562swap_checked : acceptsGraphIso
    (source (graph core1562) (root 9) 1 0) DegreeOneSmallSpectrum1399.graph sourceMap1562swap=true := by decide +kernel
theorem fusedMap1562swap_checked : acceptsGraphIso
    (fused (graph core1562) (root 9) 1 0) DegreeOneSmallSpectrum1512.graph fusedMap1562swap=true := by decide +kernel
theorem certified1562swap : Certified (graph core1562) (root 9) 1 0 :=
  of_native_maps core1562 DegreeOneSmallSpectrum1399.graph DegreeOneSmallSpectrum1512.graph
    sourceMap1562swap fusedMap1562swap sourceMap1562swap_checked fusedMap1562swap_checked
    DegreeOneSmallComparisons.comparison1562
#print axioms sourceMap1562swap_checked
#print axioms fusedMap1562swap_checked
#print axioms certified1562swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
