/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1608 : Family 9 := level9.get ⟨346,by decide⟩
def sourceMap1608 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1608 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1608_checked : acceptsGraphIso
    (source (graph core1608) (root 9) 0 1) DegreeOneSmallSpectrum1690.graph sourceMap1608=true := by decide +kernel
theorem fusedMap1608_checked : acceptsGraphIso
    (fused (graph core1608) (root 9) 0 1) DegreeOneSmallSpectrum1045.graph fusedMap1608=true := by decide +kernel
theorem certified1608 : Certified (graph core1608) (root 9) 0 1 :=
  of_native_maps core1608 DegreeOneSmallSpectrum1690.graph DegreeOneSmallSpectrum1045.graph
    sourceMap1608 fusedMap1608 sourceMap1608_checked fusedMap1608_checked
    DegreeOneSmallComparisons.comparison1608
#print axioms sourceMap1608_checked
#print axioms fusedMap1608_checked
#print axioms certified1608
def sourceMap1608swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1608swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1608swap_checked : acceptsGraphIso
    (source (graph core1608) (root 9) 1 0) DegreeOneSmallSpectrum1690.graph sourceMap1608swap=true := by decide +kernel
theorem fusedMap1608swap_checked : acceptsGraphIso
    (fused (graph core1608) (root 9) 1 0) DegreeOneSmallSpectrum1045.graph fusedMap1608swap=true := by decide +kernel
theorem certified1608swap : Certified (graph core1608) (root 9) 1 0 :=
  of_native_maps core1608 DegreeOneSmallSpectrum1690.graph DegreeOneSmallSpectrum1045.graph
    sourceMap1608swap fusedMap1608swap sourceMap1608swap_checked fusedMap1608swap_checked
    DegreeOneSmallComparisons.comparison1608
#print axioms sourceMap1608swap_checked
#print axioms fusedMap1608swap_checked
#print axioms certified1608swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
