/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1352 : Family 9 := level9.get ⟨103,by decide⟩
def sourceMap1352 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1352 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1352_checked : acceptsGraphIso
    (source (graph core1352) (root 9) 0 1) DegreeOneSmallSpectrum1450.graph sourceMap1352=true := by decide +kernel
theorem fusedMap1352_checked : acceptsGraphIso
    (fused (graph core1352) (root 9) 0 1) DegreeOneSmallSpectrum957.graph fusedMap1352=true := by decide +kernel
theorem certified1352 : Certified (graph core1352) (root 9) 0 1 :=
  of_native_maps core1352 DegreeOneSmallSpectrum1450.graph DegreeOneSmallSpectrum957.graph
    sourceMap1352 fusedMap1352 sourceMap1352_checked fusedMap1352_checked
    DegreeOneSmallComparisons.comparison1352
#print axioms sourceMap1352_checked
#print axioms fusedMap1352_checked
#print axioms certified1352
def sourceMap1352swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1352swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1352swap_checked : acceptsGraphIso
    (source (graph core1352) (root 9) 1 0) DegreeOneSmallSpectrum1450.graph sourceMap1352swap=true := by decide +kernel
theorem fusedMap1352swap_checked : acceptsGraphIso
    (fused (graph core1352) (root 9) 1 0) DegreeOneSmallSpectrum957.graph fusedMap1352swap=true := by decide +kernel
theorem certified1352swap : Certified (graph core1352) (root 9) 1 0 :=
  of_native_maps core1352 DegreeOneSmallSpectrum1450.graph DegreeOneSmallSpectrum957.graph
    sourceMap1352swap fusedMap1352swap sourceMap1352swap_checked fusedMap1352swap_checked
    DegreeOneSmallComparisons.comparison1352
#print axioms sourceMap1352swap_checked
#print axioms fusedMap1352swap_checked
#print axioms certified1352swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
