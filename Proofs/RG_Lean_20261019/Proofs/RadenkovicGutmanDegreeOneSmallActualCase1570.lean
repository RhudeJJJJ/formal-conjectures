/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1570 : Family 9 := level9.get ⟨300,by decide⟩
def sourceMap1570 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1570 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1570_checked : acceptsGraphIso
    (source (graph core1570) (root 9) 0 1) DegreeOneSmallSpectrum1415.graph sourceMap1570=true := by decide +kernel
theorem fusedMap1570_checked : acceptsGraphIso
    (fused (graph core1570) (root 9) 0 1) DegreeOneSmallSpectrum1516.graph fusedMap1570=true := by decide +kernel
theorem certified1570 : Certified (graph core1570) (root 9) 0 1 :=
  of_native_maps core1570 DegreeOneSmallSpectrum1415.graph DegreeOneSmallSpectrum1516.graph
    sourceMap1570 fusedMap1570 sourceMap1570_checked fusedMap1570_checked
    DegreeOneSmallComparisons.comparison1570
#print axioms sourceMap1570_checked
#print axioms fusedMap1570_checked
#print axioms certified1570
def sourceMap1570swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1570swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1570swap_checked : acceptsGraphIso
    (source (graph core1570) (root 9) 1 0) DegreeOneSmallSpectrum1415.graph sourceMap1570swap=true := by decide +kernel
theorem fusedMap1570swap_checked : acceptsGraphIso
    (fused (graph core1570) (root 9) 1 0) DegreeOneSmallSpectrum1516.graph fusedMap1570swap=true := by decide +kernel
theorem certified1570swap : Certified (graph core1570) (root 9) 1 0 :=
  of_native_maps core1570 DegreeOneSmallSpectrum1415.graph DegreeOneSmallSpectrum1516.graph
    sourceMap1570swap fusedMap1570swap sourceMap1570swap_checked fusedMap1570swap_checked
    DegreeOneSmallComparisons.comparison1570
#print axioms sourceMap1570swap_checked
#print axioms fusedMap1570swap_checked
#print axioms certified1570swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
