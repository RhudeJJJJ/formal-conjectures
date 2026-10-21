/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1520 : Family 9 := level9.get ⟨252,by decide⟩
def sourceMap1520 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1520 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1520_checked : acceptsGraphIso
    (source (graph core1520) (root 9) 0 1) DegreeOneSmallSpectrum1427.graph sourceMap1520=true := by decide +kernel
theorem fusedMap1520_checked : acceptsGraphIso
    (fused (graph core1520) (root 9) 0 1) DegreeOneSmallSpectrum1463.graph fusedMap1520=true := by decide +kernel
theorem certified1520 : Certified (graph core1520) (root 9) 0 1 :=
  of_native_maps core1520 DegreeOneSmallSpectrum1427.graph DegreeOneSmallSpectrum1463.graph
    sourceMap1520 fusedMap1520 sourceMap1520_checked fusedMap1520_checked
    DegreeOneSmallComparisons.comparison1520
#print axioms sourceMap1520_checked
#print axioms fusedMap1520_checked
#print axioms certified1520
def sourceMap1520swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1520swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1520swap_checked : acceptsGraphIso
    (source (graph core1520) (root 9) 1 0) DegreeOneSmallSpectrum1427.graph sourceMap1520swap=true := by decide +kernel
theorem fusedMap1520swap_checked : acceptsGraphIso
    (fused (graph core1520) (root 9) 1 0) DegreeOneSmallSpectrum1463.graph fusedMap1520swap=true := by decide +kernel
theorem certified1520swap : Certified (graph core1520) (root 9) 1 0 :=
  of_native_maps core1520 DegreeOneSmallSpectrum1427.graph DegreeOneSmallSpectrum1463.graph
    sourceMap1520swap fusedMap1520swap sourceMap1520swap_checked fusedMap1520swap_checked
    DegreeOneSmallComparisons.comparison1520
#print axioms sourceMap1520swap_checked
#print axioms fusedMap1520swap_checked
#print axioms certified1520swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
