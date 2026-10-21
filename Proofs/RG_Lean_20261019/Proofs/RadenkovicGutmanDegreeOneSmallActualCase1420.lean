/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1420 : Family 9 := level9.get ⟨161,by decide⟩
def sourceMap1420 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1420 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1420_checked : acceptsGraphIso
    (source (graph core1420) (root 9) 0 1) DegreeOneSmallSpectrum1116.graph sourceMap1420=true := by decide +kernel
theorem fusedMap1420_checked : acceptsGraphIso
    (fused (graph core1420) (root 9) 0 1) DegreeOneSmallSpectrum1118.graph fusedMap1420=true := by decide +kernel
theorem certified1420 : Certified (graph core1420) (root 9) 0 1 :=
  of_native_maps core1420 DegreeOneSmallSpectrum1116.graph DegreeOneSmallSpectrum1118.graph
    sourceMap1420 fusedMap1420 sourceMap1420_checked fusedMap1420_checked
    DegreeOneSmallComparisons.comparison1420
#print axioms sourceMap1420_checked
#print axioms fusedMap1420_checked
#print axioms certified1420
def sourceMap1420swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1420swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1420swap_checked : acceptsGraphIso
    (source (graph core1420) (root 9) 1 0) DegreeOneSmallSpectrum1116.graph sourceMap1420swap=true := by decide +kernel
theorem fusedMap1420swap_checked : acceptsGraphIso
    (fused (graph core1420) (root 9) 1 0) DegreeOneSmallSpectrum1118.graph fusedMap1420swap=true := by decide +kernel
theorem certified1420swap : Certified (graph core1420) (root 9) 1 0 :=
  of_native_maps core1420 DegreeOneSmallSpectrum1116.graph DegreeOneSmallSpectrum1118.graph
    sourceMap1420swap fusedMap1420swap sourceMap1420swap_checked fusedMap1420swap_checked
    DegreeOneSmallComparisons.comparison1420
#print axioms sourceMap1420swap_checked
#print axioms fusedMap1420swap_checked
#print axioms certified1420swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
