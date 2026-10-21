/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1033 : Family 8 := level8.get ⟨113,by decide⟩
def sourceMap1033 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1033 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1033_checked : acceptsGraphIso
    (source (graph core1033) (root 8) 0 2) DegreeOneSmallSpectrum1123.graph sourceMap1033=true := by decide +kernel
theorem fusedMap1033_checked : acceptsGraphIso
    (fused (graph core1033) (root 8) 0 2) DegreeOneSmallSpectrum1124.graph fusedMap1033=true := by decide +kernel
theorem certified1033 : Certified (graph core1033) (root 8) 0 2 :=
  of_native_maps core1033 DegreeOneSmallSpectrum1123.graph DegreeOneSmallSpectrum1124.graph
    sourceMap1033 fusedMap1033 sourceMap1033_checked fusedMap1033_checked
    DegreeOneSmallComparisons.comparison1033
#print axioms sourceMap1033_checked
#print axioms fusedMap1033_checked
#print axioms certified1033
def sourceMap1033swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1033swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1033swap_checked : acceptsGraphIso
    (source (graph core1033) (root 8) 2 0) DegreeOneSmallSpectrum1123.graph sourceMap1033swap=true := by decide +kernel
theorem fusedMap1033swap_checked : acceptsGraphIso
    (fused (graph core1033) (root 8) 2 0) DegreeOneSmallSpectrum1124.graph fusedMap1033swap=true := by decide +kernel
theorem certified1033swap : Certified (graph core1033) (root 8) 2 0 :=
  of_native_maps core1033 DegreeOneSmallSpectrum1123.graph DegreeOneSmallSpectrum1124.graph
    sourceMap1033swap fusedMap1033swap sourceMap1033swap_checked fusedMap1033swap_checked
    DegreeOneSmallComparisons.comparison1033
#print axioms sourceMap1033swap_checked
#print axioms fusedMap1033swap_checked
#print axioms certified1033swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
