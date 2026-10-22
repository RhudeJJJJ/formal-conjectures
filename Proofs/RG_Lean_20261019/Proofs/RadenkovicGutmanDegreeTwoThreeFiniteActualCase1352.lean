/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1352 : Family 9 := level9.get ⟨481,by decide⟩
def sourceMap1352 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,13,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1352 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1352_checked : acceptsGraphIso
    (source (graph core1352) (root 9) 0 2) DegreeTwoThreeSpectrum2169.graph sourceMap1352=true := by decide +kernel
theorem fusedMap1352_checked : acceptsGraphIso
    (fused (graph core1352) (root 9) 0 2) DegreeTwoThreeSpectrum2178.graph fusedMap1352=true := by decide +kernel
theorem certified1352 : Certified (graph core1352) (root 9) 0 2 :=
  of_native_maps core1352 DegreeTwoThreeSpectrum2169.graph DegreeTwoThreeSpectrum2178.graph
    sourceMap1352 fusedMap1352 sourceMap1352_checked fusedMap1352_checked
    DegreeTwoThreeFiniteComparisons.comparison1352
#print axioms sourceMap1352_checked
#print axioms fusedMap1352_checked
#print axioms certified1352
def sourceMap1352swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8,13] (sourceLabel 9 2 0 v)
def fusedMap1352swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1352swap_checked : acceptsGraphIso
    (source (graph core1352) (root 9) 2 0) DegreeTwoThreeSpectrum2169.graph sourceMap1352swap=true := by decide +kernel
theorem fusedMap1352swap_checked : acceptsGraphIso
    (fused (graph core1352) (root 9) 2 0) DegreeTwoThreeSpectrum2178.graph fusedMap1352swap=true := by decide +kernel
theorem certified1352swap : Certified (graph core1352) (root 9) 2 0 :=
  of_native_maps core1352 DegreeTwoThreeSpectrum2169.graph DegreeTwoThreeSpectrum2178.graph
    sourceMap1352swap fusedMap1352swap sourceMap1352swap_checked fusedMap1352swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1352
#print axioms sourceMap1352swap_checked
#print axioms fusedMap1352swap_checked
#print axioms certified1352swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
