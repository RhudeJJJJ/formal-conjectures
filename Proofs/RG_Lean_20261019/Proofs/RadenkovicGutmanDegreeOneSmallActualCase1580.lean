/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1580 : Family 9 := level9.get ⟨322,by decide⟩
def sourceMap1580 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1580 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1580_checked : acceptsGraphIso
    (source (graph core1580) (root 9) 0 1) DegreeOneSmallSpectrum1576.graph sourceMap1580=true := by decide +kernel
theorem fusedMap1580_checked : acceptsGraphIso
    (fused (graph core1580) (root 9) 0 1) DegreeOneSmallSpectrum987.graph fusedMap1580=true := by decide +kernel
theorem certified1580 : Certified (graph core1580) (root 9) 0 1 :=
  of_native_maps core1580 DegreeOneSmallSpectrum1576.graph DegreeOneSmallSpectrum987.graph
    sourceMap1580 fusedMap1580 sourceMap1580_checked fusedMap1580_checked
    DegreeOneSmallComparisons.comparison1580
#print axioms sourceMap1580_checked
#print axioms fusedMap1580_checked
#print axioms certified1580
def sourceMap1580swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1580swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1580swap_checked : acceptsGraphIso
    (source (graph core1580) (root 9) 1 0) DegreeOneSmallSpectrum1576.graph sourceMap1580swap=true := by decide +kernel
theorem fusedMap1580swap_checked : acceptsGraphIso
    (fused (graph core1580) (root 9) 1 0) DegreeOneSmallSpectrum987.graph fusedMap1580swap=true := by decide +kernel
theorem certified1580swap : Certified (graph core1580) (root 9) 1 0 :=
  of_native_maps core1580 DegreeOneSmallSpectrum1576.graph DegreeOneSmallSpectrum987.graph
    sourceMap1580swap fusedMap1580swap sourceMap1580swap_checked fusedMap1580swap_checked
    DegreeOneSmallComparisons.comparison1580
#print axioms sourceMap1580swap_checked
#print axioms fusedMap1580swap_checked
#print axioms certified1580swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
