/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1438 : Family 9 := level9.get ⟨175,by decide⟩
def sourceMap1438 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1438 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1438_checked : acceptsGraphIso
    (source (graph core1438) (root 9) 0 1) DegreeOneSmallSpectrum1193.graph sourceMap1438=true := by decide +kernel
theorem fusedMap1438_checked : acceptsGraphIso
    (fused (graph core1438) (root 9) 0 1) DegreeOneSmallSpectrum1195.graph fusedMap1438=true := by decide +kernel
theorem certified1438 : Certified (graph core1438) (root 9) 0 1 :=
  of_native_maps core1438 DegreeOneSmallSpectrum1193.graph DegreeOneSmallSpectrum1195.graph
    sourceMap1438 fusedMap1438 sourceMap1438_checked fusedMap1438_checked
    DegreeOneSmallComparisons.comparison1438
#print axioms sourceMap1438_checked
#print axioms fusedMap1438_checked
#print axioms certified1438
def sourceMap1438swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1438swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1438swap_checked : acceptsGraphIso
    (source (graph core1438) (root 9) 1 0) DegreeOneSmallSpectrum1193.graph sourceMap1438swap=true := by decide +kernel
theorem fusedMap1438swap_checked : acceptsGraphIso
    (fused (graph core1438) (root 9) 1 0) DegreeOneSmallSpectrum1195.graph fusedMap1438swap=true := by decide +kernel
theorem certified1438swap : Certified (graph core1438) (root 9) 1 0 :=
  of_native_maps core1438 DegreeOneSmallSpectrum1193.graph DegreeOneSmallSpectrum1195.graph
    sourceMap1438swap fusedMap1438swap sourceMap1438swap_checked fusedMap1438swap_checked
    DegreeOneSmallComparisons.comparison1438
#print axioms sourceMap1438swap_checked
#print axioms fusedMap1438swap_checked
#print axioms certified1438swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
