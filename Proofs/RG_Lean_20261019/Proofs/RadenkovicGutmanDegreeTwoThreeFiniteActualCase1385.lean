/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1385 : Family 9 := level9.get ⟨566,by decide⟩
def sourceMap1385 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1385 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1385_checked : acceptsGraphIso
    (source (graph core1385) (root 9) 0 2) DegreeTwoThreeSpectrum2256.graph sourceMap1385=true := by decide +kernel
theorem fusedMap1385_checked : acceptsGraphIso
    (fused (graph core1385) (root 9) 0 2) DegreeTwoThreeSpectrum1952.graph fusedMap1385=true := by decide +kernel
theorem certified1385 : Certified (graph core1385) (root 9) 0 2 :=
  of_native_maps core1385 DegreeTwoThreeSpectrum2256.graph DegreeTwoThreeSpectrum1952.graph
    sourceMap1385 fusedMap1385 sourceMap1385_checked fusedMap1385_checked
    DegreeTwoThreeFiniteComparisons.comparison1385
#print axioms sourceMap1385_checked
#print axioms fusedMap1385_checked
#print axioms certified1385
def sourceMap1385swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1385swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1385swap_checked : acceptsGraphIso
    (source (graph core1385) (root 9) 2 0) DegreeTwoThreeSpectrum2256.graph sourceMap1385swap=true := by decide +kernel
theorem fusedMap1385swap_checked : acceptsGraphIso
    (fused (graph core1385) (root 9) 2 0) DegreeTwoThreeSpectrum1952.graph fusedMap1385swap=true := by decide +kernel
theorem certified1385swap : Certified (graph core1385) (root 9) 2 0 :=
  of_native_maps core1385 DegreeTwoThreeSpectrum2256.graph DegreeTwoThreeSpectrum1952.graph
    sourceMap1385swap fusedMap1385swap sourceMap1385swap_checked fusedMap1385swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1385
#print axioms sourceMap1385swap_checked
#print axioms fusedMap1385swap_checked
#print axioms certified1385swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
