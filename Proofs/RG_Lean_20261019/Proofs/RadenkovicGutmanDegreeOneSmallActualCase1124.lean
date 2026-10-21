/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1124 : Family 8 := level8.get ⟨166,by decide⟩
def sourceMap1124 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap1124 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1124_checked : acceptsGraphIso
    (source (graph core1124) (root 8) 0 1) DegreeOneSmallSpectrum819.graph sourceMap1124=true := by decide +kernel
theorem fusedMap1124_checked : acceptsGraphIso
    (fused (graph core1124) (root 8) 0 1) DegreeOneSmallSpectrum568.graph fusedMap1124=true := by decide +kernel
theorem certified1124 : Certified (graph core1124) (root 8) 0 1 :=
  of_native_maps core1124 DegreeOneSmallSpectrum819.graph DegreeOneSmallSpectrum568.graph
    sourceMap1124 fusedMap1124 sourceMap1124_checked fusedMap1124_checked
    DegreeOneSmallComparisons.comparison1124
#print axioms sourceMap1124_checked
#print axioms fusedMap1124_checked
#print axioms certified1124
def sourceMap1124swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap1124swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1124swap_checked : acceptsGraphIso
    (source (graph core1124) (root 8) 1 0) DegreeOneSmallSpectrum819.graph sourceMap1124swap=true := by decide +kernel
theorem fusedMap1124swap_checked : acceptsGraphIso
    (fused (graph core1124) (root 8) 1 0) DegreeOneSmallSpectrum568.graph fusedMap1124swap=true := by decide +kernel
theorem certified1124swap : Certified (graph core1124) (root 8) 1 0 :=
  of_native_maps core1124 DegreeOneSmallSpectrum819.graph DegreeOneSmallSpectrum568.graph
    sourceMap1124swap fusedMap1124swap sourceMap1124swap_checked fusedMap1124swap_checked
    DegreeOneSmallComparisons.comparison1124
#print axioms sourceMap1124swap_checked
#print axioms fusedMap1124swap_checked
#print axioms certified1124swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
