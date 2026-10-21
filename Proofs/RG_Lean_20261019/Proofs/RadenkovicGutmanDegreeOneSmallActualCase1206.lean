/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1206 : Family 9 := level9.get ⟨5,by decide⟩
def sourceMap1206 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 9 0 1 v)
def fusedMap1206 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1206_checked : acceptsGraphIso
    (source (graph core1206) (root 9) 0 1) DegreeOneSmallSpectrum944.graph sourceMap1206=true := by decide +kernel
theorem fusedMap1206_checked : acceptsGraphIso
    (fused (graph core1206) (root 9) 0 1) DegreeOneSmallSpectrum860.graph fusedMap1206=true := by decide +kernel
theorem certified1206 : Certified (graph core1206) (root 9) 0 1 :=
  of_native_maps core1206 DegreeOneSmallSpectrum944.graph DegreeOneSmallSpectrum860.graph
    sourceMap1206 fusedMap1206 sourceMap1206_checked fusedMap1206_checked
    DegreeOneSmallComparisons.comparison1206
#print axioms sourceMap1206_checked
#print axioms fusedMap1206_checked
#print axioms certified1206
def sourceMap1206swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 9 1 0 v)
def fusedMap1206swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1206swap_checked : acceptsGraphIso
    (source (graph core1206) (root 9) 1 0) DegreeOneSmallSpectrum944.graph sourceMap1206swap=true := by decide +kernel
theorem fusedMap1206swap_checked : acceptsGraphIso
    (fused (graph core1206) (root 9) 1 0) DegreeOneSmallSpectrum860.graph fusedMap1206swap=true := by decide +kernel
theorem certified1206swap : Certified (graph core1206) (root 9) 1 0 :=
  of_native_maps core1206 DegreeOneSmallSpectrum944.graph DegreeOneSmallSpectrum860.graph
    sourceMap1206swap fusedMap1206swap sourceMap1206swap_checked fusedMap1206swap_checked
    DegreeOneSmallComparisons.comparison1206
#print axioms sourceMap1206swap_checked
#print axioms fusedMap1206swap_checked
#print axioms certified1206swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
