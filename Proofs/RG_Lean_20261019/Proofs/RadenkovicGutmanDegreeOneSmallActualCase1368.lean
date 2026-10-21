/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1368 : Family 9 := level9.get ⟨115,by decide⟩
def sourceMap1368 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1368 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1368_checked : acceptsGraphIso
    (source (graph core1368) (root 9) 0 1) DegreeOneSmallSpectrum1434.graph sourceMap1368=true := by decide +kernel
theorem fusedMap1368_checked : acceptsGraphIso
    (fused (graph core1368) (root 9) 0 1) DegreeOneSmallSpectrum970.graph fusedMap1368=true := by decide +kernel
theorem certified1368 : Certified (graph core1368) (root 9) 0 1 :=
  of_native_maps core1368 DegreeOneSmallSpectrum1434.graph DegreeOneSmallSpectrum970.graph
    sourceMap1368 fusedMap1368 sourceMap1368_checked fusedMap1368_checked
    DegreeOneSmallComparisons.comparison1368
#print axioms sourceMap1368_checked
#print axioms fusedMap1368_checked
#print axioms certified1368
def sourceMap1368swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1368swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1368swap_checked : acceptsGraphIso
    (source (graph core1368) (root 9) 1 0) DegreeOneSmallSpectrum1434.graph sourceMap1368swap=true := by decide +kernel
theorem fusedMap1368swap_checked : acceptsGraphIso
    (fused (graph core1368) (root 9) 1 0) DegreeOneSmallSpectrum970.graph fusedMap1368swap=true := by decide +kernel
theorem certified1368swap : Certified (graph core1368) (root 9) 1 0 :=
  of_native_maps core1368 DegreeOneSmallSpectrum1434.graph DegreeOneSmallSpectrum970.graph
    sourceMap1368swap fusedMap1368swap sourceMap1368swap_checked fusedMap1368swap_checked
    DegreeOneSmallComparisons.comparison1368
#print axioms sourceMap1368swap_checked
#print axioms fusedMap1368swap_checked
#print axioms certified1368swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
