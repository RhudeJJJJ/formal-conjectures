/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1196 : Family 9 := level9.get ⟨0,by decide⟩
def sourceMap1196 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 9 0 1 v)
def fusedMap1196 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (fusedLabel 9 0 1 v)
theorem sourceMap1196_checked : acceptsGraphIso
    (source (graph core1196) (root 9) 0 1) DegreeOneSmallSpectrum857.graph sourceMap1196=true := by decide +kernel
theorem fusedMap1196_checked : acceptsGraphIso
    (fused (graph core1196) (root 9) 0 1) DegreeOneSmallSpectrum861.graph fusedMap1196=true := by decide +kernel
theorem certified1196 : Certified (graph core1196) (root 9) 0 1 :=
  of_native_maps core1196 DegreeOneSmallSpectrum857.graph DegreeOneSmallSpectrum861.graph
    sourceMap1196 fusedMap1196 sourceMap1196_checked fusedMap1196_checked
    DegreeOneSmallComparisons.comparison1196
#print axioms sourceMap1196_checked
#print axioms fusedMap1196_checked
#print axioms certified1196
def sourceMap1196swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 9 1 0 v)
def fusedMap1196swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (fusedLabel 9 1 0 v)
theorem sourceMap1196swap_checked : acceptsGraphIso
    (source (graph core1196) (root 9) 1 0) DegreeOneSmallSpectrum857.graph sourceMap1196swap=true := by decide +kernel
theorem fusedMap1196swap_checked : acceptsGraphIso
    (fused (graph core1196) (root 9) 1 0) DegreeOneSmallSpectrum861.graph fusedMap1196swap=true := by decide +kernel
theorem certified1196swap : Certified (graph core1196) (root 9) 1 0 :=
  of_native_maps core1196 DegreeOneSmallSpectrum857.graph DegreeOneSmallSpectrum861.graph
    sourceMap1196swap fusedMap1196swap sourceMap1196swap_checked fusedMap1196swap_checked
    DegreeOneSmallComparisons.comparison1196
#print axioms sourceMap1196swap_checked
#print axioms fusedMap1196swap_checked
#print axioms certified1196swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
