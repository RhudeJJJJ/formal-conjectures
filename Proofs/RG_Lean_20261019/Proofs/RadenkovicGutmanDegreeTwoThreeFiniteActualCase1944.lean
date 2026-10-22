/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1944 : Family 10 := level10.get ⟨1470,by decide⟩
def sourceMap1944 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,4,5,6,7,8,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1944 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1944_checked : acceptsGraphIso
    (source (graph core1944) (root 10) 0 2) DegreeTwoThreeSpectrum3643.graph sourceMap1944=true := by decide +kernel
theorem fusedMap1944_checked : acceptsGraphIso
    (fused (graph core1944) (root 10) 0 2) DegreeTwoThreeSpectrum3711.graph fusedMap1944=true := by decide +kernel
theorem certified1944 : Certified (graph core1944) (root 10) 0 2 :=
  of_native_maps core1944 DegreeTwoThreeSpectrum3643.graph DegreeTwoThreeSpectrum3711.graph
    sourceMap1944 fusedMap1944 sourceMap1944_checked fusedMap1944_checked
    DegreeTwoThreeFiniteComparisons.comparison1944
#print axioms sourceMap1944_checked
#print axioms fusedMap1944_checked
#print axioms certified1944
def sourceMap1944swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,4,5,6,7,1,2,3,8] (sourceLabel 10 2 0 v)
def fusedMap1944swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1944swap_checked : acceptsGraphIso
    (source (graph core1944) (root 10) 2 0) DegreeTwoThreeSpectrum3643.graph sourceMap1944swap=true := by decide +kernel
theorem fusedMap1944swap_checked : acceptsGraphIso
    (fused (graph core1944) (root 10) 2 0) DegreeTwoThreeSpectrum3711.graph fusedMap1944swap=true := by decide +kernel
theorem certified1944swap : Certified (graph core1944) (root 10) 2 0 :=
  of_native_maps core1944 DegreeTwoThreeSpectrum3643.graph DegreeTwoThreeSpectrum3711.graph
    sourceMap1944swap fusedMap1944swap sourceMap1944swap_checked fusedMap1944swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1944
#print axioms sourceMap1944swap_checked
#print axioms fusedMap1944swap_checked
#print axioms certified1944swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
