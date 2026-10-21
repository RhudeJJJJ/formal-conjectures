/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1278 : Family 9 := level9.get ⟨51,by decide⟩
def sourceMap1278 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1278 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1278_checked : acceptsGraphIso
    (source (graph core1278) (root 9) 0 1) DegreeOneSmallSpectrum1154.graph sourceMap1278=true := by decide +kernel
theorem fusedMap1278_checked : acceptsGraphIso
    (fused (graph core1278) (root 9) 0 1) DegreeOneSmallSpectrum873.graph fusedMap1278=true := by decide +kernel
theorem certified1278 : Certified (graph core1278) (root 9) 0 1 :=
  of_native_maps core1278 DegreeOneSmallSpectrum1154.graph DegreeOneSmallSpectrum873.graph
    sourceMap1278 fusedMap1278 sourceMap1278_checked fusedMap1278_checked
    DegreeOneSmallComparisons.comparison1278
#print axioms sourceMap1278_checked
#print axioms fusedMap1278_checked
#print axioms certified1278
def sourceMap1278swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1278swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1278swap_checked : acceptsGraphIso
    (source (graph core1278) (root 9) 1 0) DegreeOneSmallSpectrum1154.graph sourceMap1278swap=true := by decide +kernel
theorem fusedMap1278swap_checked : acceptsGraphIso
    (fused (graph core1278) (root 9) 1 0) DegreeOneSmallSpectrum873.graph fusedMap1278swap=true := by decide +kernel
theorem certified1278swap : Certified (graph core1278) (root 9) 1 0 :=
  of_native_maps core1278 DegreeOneSmallSpectrum1154.graph DegreeOneSmallSpectrum873.graph
    sourceMap1278swap fusedMap1278swap sourceMap1278swap_checked fusedMap1278swap_checked
    DegreeOneSmallComparisons.comparison1278
#print axioms sourceMap1278swap_checked
#print axioms fusedMap1278swap_checked
#print axioms certified1278swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
