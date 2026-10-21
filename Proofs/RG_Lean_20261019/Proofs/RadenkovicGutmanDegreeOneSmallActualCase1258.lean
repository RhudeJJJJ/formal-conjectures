/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1258 : Family 9 := level9.get ⟨36,by decide⟩
def sourceMap1258 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1258 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1258_checked : acceptsGraphIso
    (source (graph core1258) (root 9) 0 1) DegreeOneSmallSpectrum925.graph sourceMap1258=true := by decide +kernel
theorem fusedMap1258_checked : acceptsGraphIso
    (fused (graph core1258) (root 9) 0 1) DegreeOneSmallSpectrum976.graph fusedMap1258=true := by decide +kernel
theorem certified1258 : Certified (graph core1258) (root 9) 0 1 :=
  of_native_maps core1258 DegreeOneSmallSpectrum925.graph DegreeOneSmallSpectrum976.graph
    sourceMap1258 fusedMap1258 sourceMap1258_checked fusedMap1258_checked
    DegreeOneSmallComparisons.comparison1258
#print axioms sourceMap1258_checked
#print axioms fusedMap1258_checked
#print axioms certified1258
def sourceMap1258swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1258swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1258swap_checked : acceptsGraphIso
    (source (graph core1258) (root 9) 1 0) DegreeOneSmallSpectrum925.graph sourceMap1258swap=true := by decide +kernel
theorem fusedMap1258swap_checked : acceptsGraphIso
    (fused (graph core1258) (root 9) 1 0) DegreeOneSmallSpectrum976.graph fusedMap1258swap=true := by decide +kernel
theorem certified1258swap : Certified (graph core1258) (root 9) 1 0 :=
  of_native_maps core1258 DegreeOneSmallSpectrum925.graph DegreeOneSmallSpectrum976.graph
    sourceMap1258swap fusedMap1258swap sourceMap1258swap_checked fusedMap1258swap_checked
    DegreeOneSmallComparisons.comparison1258
#print axioms sourceMap1258swap_checked
#print axioms fusedMap1258swap_checked
#print axioms certified1258swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
