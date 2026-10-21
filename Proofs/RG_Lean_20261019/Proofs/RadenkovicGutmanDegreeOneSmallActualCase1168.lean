/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1168 : Family 8 := level8.get ⟨209,by decide⟩
def sourceMap1168 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1168 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1168_checked : acceptsGraphIso
    (source (graph core1168) (root 8) 0 1) DegreeOneSmallSpectrum686.graph sourceMap1168=true := by decide +kernel
theorem fusedMap1168_checked : acceptsGraphIso
    (fused (graph core1168) (root 8) 0 1) DegreeOneSmallSpectrum687.graph fusedMap1168=true := by decide +kernel
theorem certified1168 : Certified (graph core1168) (root 8) 0 1 :=
  of_native_maps core1168 DegreeOneSmallSpectrum686.graph DegreeOneSmallSpectrum687.graph
    sourceMap1168 fusedMap1168 sourceMap1168_checked fusedMap1168_checked
    DegreeOneSmallComparisons.comparison1168
#print axioms sourceMap1168_checked
#print axioms fusedMap1168_checked
#print axioms certified1168
def sourceMap1168swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1168swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1168swap_checked : acceptsGraphIso
    (source (graph core1168) (root 8) 1 0) DegreeOneSmallSpectrum686.graph sourceMap1168swap=true := by decide +kernel
theorem fusedMap1168swap_checked : acceptsGraphIso
    (fused (graph core1168) (root 8) 1 0) DegreeOneSmallSpectrum687.graph fusedMap1168swap=true := by decide +kernel
theorem certified1168swap : Certified (graph core1168) (root 8) 1 0 :=
  of_native_maps core1168 DegreeOneSmallSpectrum686.graph DegreeOneSmallSpectrum687.graph
    sourceMap1168swap fusedMap1168swap sourceMap1168swap_checked fusedMap1168swap_checked
    DegreeOneSmallComparisons.comparison1168
#print axioms sourceMap1168swap_checked
#print axioms fusedMap1168swap_checked
#print axioms certified1168swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
