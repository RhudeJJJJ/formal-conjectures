/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1640 : Family 9 := level9.get ⟨386,by decide⟩
def sourceMap1640 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1640 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1640_checked : acceptsGraphIso
    (source (graph core1640) (root 9) 0 1) DegreeOneSmallSpectrum1840.graph sourceMap1640=true := by decide +kernel
theorem fusedMap1640_checked : acceptsGraphIso
    (fused (graph core1640) (root 9) 0 1) DegreeOneSmallSpectrum1183.graph fusedMap1640=true := by decide +kernel
theorem certified1640 : Certified (graph core1640) (root 9) 0 1 :=
  of_native_maps core1640 DegreeOneSmallSpectrum1840.graph DegreeOneSmallSpectrum1183.graph
    sourceMap1640 fusedMap1640 sourceMap1640_checked fusedMap1640_checked
    DegreeOneSmallComparisons.comparison1640
#print axioms sourceMap1640_checked
#print axioms fusedMap1640_checked
#print axioms certified1640
def sourceMap1640swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1640swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1640swap_checked : acceptsGraphIso
    (source (graph core1640) (root 9) 1 0) DegreeOneSmallSpectrum1840.graph sourceMap1640swap=true := by decide +kernel
theorem fusedMap1640swap_checked : acceptsGraphIso
    (fused (graph core1640) (root 9) 1 0) DegreeOneSmallSpectrum1183.graph fusedMap1640swap=true := by decide +kernel
theorem certified1640swap : Certified (graph core1640) (root 9) 1 0 :=
  of_native_maps core1640 DegreeOneSmallSpectrum1840.graph DegreeOneSmallSpectrum1183.graph
    sourceMap1640swap fusedMap1640swap sourceMap1640swap_checked fusedMap1640swap_checked
    DegreeOneSmallComparisons.comparison1640
#print axioms sourceMap1640swap_checked
#print axioms fusedMap1640swap_checked
#print axioms certified1640swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
