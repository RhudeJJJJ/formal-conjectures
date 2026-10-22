/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1380 : Family 9 := level9.get ⟨554,by decide⟩
def sourceMap1380 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1380 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1380_checked : acceptsGraphIso
    (source (graph core1380) (root 9) 0 2) DegreeTwoThreeSpectrum2251.graph sourceMap1380=true := by decide +kernel
theorem fusedMap1380_checked : acceptsGraphIso
    (fused (graph core1380) (root 9) 0 2) DegreeTwoThreeSpectrum1935.graph fusedMap1380=true := by decide +kernel
theorem certified1380 : Certified (graph core1380) (root 9) 0 2 :=
  of_native_maps core1380 DegreeTwoThreeSpectrum2251.graph DegreeTwoThreeSpectrum1935.graph
    sourceMap1380 fusedMap1380 sourceMap1380_checked fusedMap1380_checked
    DegreeTwoThreeFiniteComparisons.comparison1380
#print axioms sourceMap1380_checked
#print axioms fusedMap1380_checked
#print axioms certified1380
def sourceMap1380swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1380swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1380swap_checked : acceptsGraphIso
    (source (graph core1380) (root 9) 2 0) DegreeTwoThreeSpectrum2251.graph sourceMap1380swap=true := by decide +kernel
theorem fusedMap1380swap_checked : acceptsGraphIso
    (fused (graph core1380) (root 9) 2 0) DegreeTwoThreeSpectrum1935.graph fusedMap1380swap=true := by decide +kernel
theorem certified1380swap : Certified (graph core1380) (root 9) 2 0 :=
  of_native_maps core1380 DegreeTwoThreeSpectrum2251.graph DegreeTwoThreeSpectrum1935.graph
    sourceMap1380swap fusedMap1380swap sourceMap1380swap_checked fusedMap1380swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1380
#print axioms sourceMap1380swap_checked
#print axioms fusedMap1380swap_checked
#print axioms certified1380swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
