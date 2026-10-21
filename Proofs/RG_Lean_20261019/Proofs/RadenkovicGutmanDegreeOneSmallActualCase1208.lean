/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1208 : Family 9 := level9.get ⟨6,by decide⟩
def sourceMap1208 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 9 0 1 v)
def fusedMap1208 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1208_checked : acceptsGraphIso
    (source (graph core1208) (root 9) 0 1) DegreeOneSmallSpectrum935.graph sourceMap1208=true := by decide +kernel
theorem fusedMap1208_checked : acceptsGraphIso
    (fused (graph core1208) (root 9) 0 1) DegreeOneSmallSpectrum860.graph fusedMap1208=true := by decide +kernel
theorem certified1208 : Certified (graph core1208) (root 9) 0 1 :=
  of_native_maps core1208 DegreeOneSmallSpectrum935.graph DegreeOneSmallSpectrum860.graph
    sourceMap1208 fusedMap1208 sourceMap1208_checked fusedMap1208_checked
    DegreeOneSmallComparisons.comparison1208
#print axioms sourceMap1208_checked
#print axioms fusedMap1208_checked
#print axioms certified1208
def sourceMap1208swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 9 1 0 v)
def fusedMap1208swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1208swap_checked : acceptsGraphIso
    (source (graph core1208) (root 9) 1 0) DegreeOneSmallSpectrum935.graph sourceMap1208swap=true := by decide +kernel
theorem fusedMap1208swap_checked : acceptsGraphIso
    (fused (graph core1208) (root 9) 1 0) DegreeOneSmallSpectrum860.graph fusedMap1208swap=true := by decide +kernel
theorem certified1208swap : Certified (graph core1208) (root 9) 1 0 :=
  of_native_maps core1208 DegreeOneSmallSpectrum935.graph DegreeOneSmallSpectrum860.graph
    sourceMap1208swap fusedMap1208swap sourceMap1208swap_checked fusedMap1208swap_checked
    DegreeOneSmallComparisons.comparison1208
#print axioms sourceMap1208swap_checked
#print axioms fusedMap1208swap_checked
#print axioms certified1208swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
