/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1566 : Family 9 := level9.get ⟨295,by decide⟩
def sourceMap1566 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1566 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1566_checked : acceptsGraphIso
    (source (graph core1566) (root 9) 0 1) DegreeOneSmallSpectrum1404.graph sourceMap1566=true := by decide +kernel
theorem fusedMap1566_checked : acceptsGraphIso
    (fused (graph core1566) (root 9) 0 1) DegreeOneSmallSpectrum1514.graph fusedMap1566=true := by decide +kernel
theorem certified1566 : Certified (graph core1566) (root 9) 0 1 :=
  of_native_maps core1566 DegreeOneSmallSpectrum1404.graph DegreeOneSmallSpectrum1514.graph
    sourceMap1566 fusedMap1566 sourceMap1566_checked fusedMap1566_checked
    DegreeOneSmallComparisons.comparison1566
#print axioms sourceMap1566_checked
#print axioms fusedMap1566_checked
#print axioms certified1566
def sourceMap1566swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1566swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1566swap_checked : acceptsGraphIso
    (source (graph core1566) (root 9) 1 0) DegreeOneSmallSpectrum1404.graph sourceMap1566swap=true := by decide +kernel
theorem fusedMap1566swap_checked : acceptsGraphIso
    (fused (graph core1566) (root 9) 1 0) DegreeOneSmallSpectrum1514.graph fusedMap1566swap=true := by decide +kernel
theorem certified1566swap : Certified (graph core1566) (root 9) 1 0 :=
  of_native_maps core1566 DegreeOneSmallSpectrum1404.graph DegreeOneSmallSpectrum1514.graph
    sourceMap1566swap fusedMap1566swap sourceMap1566swap_checked fusedMap1566swap_checked
    DegreeOneSmallComparisons.comparison1566
#print axioms sourceMap1566swap_checked
#print axioms fusedMap1566swap_checked
#print axioms certified1566swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
