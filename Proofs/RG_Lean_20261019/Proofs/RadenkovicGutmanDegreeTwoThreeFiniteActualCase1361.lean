/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1361 : Family 9 := level9.get ⟨505,by decide⟩
def sourceMap1361 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,1,2,3,7,4,5,6] (sourceLabel 9 0 2 v)
def fusedMap1361 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1361_checked : acceptsGraphIso
    (source (graph core1361) (root 9) 0 2) DegreeTwoThreeSpectrum2183.graph sourceMap1361=true := by decide +kernel
theorem fusedMap1361_checked : acceptsGraphIso
    (fused (graph core1361) (root 9) 0 2) DegreeTwoThreeSpectrum2216.graph fusedMap1361=true := by decide +kernel
theorem certified1361 : Certified (graph core1361) (root 9) 0 2 :=
  of_native_maps core1361 DegreeTwoThreeSpectrum2183.graph DegreeTwoThreeSpectrum2216.graph
    sourceMap1361 fusedMap1361 sourceMap1361_checked fusedMap1361_checked
    DegreeTwoThreeFiniteComparisons.comparison1361
#print axioms sourceMap1361_checked
#print axioms fusedMap1361_checked
#print axioms certified1361
def sourceMap1361swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,1,2,3,4,5,6,7] (sourceLabel 9 2 0 v)
def fusedMap1361swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1361swap_checked : acceptsGraphIso
    (source (graph core1361) (root 9) 2 0) DegreeTwoThreeSpectrum2183.graph sourceMap1361swap=true := by decide +kernel
theorem fusedMap1361swap_checked : acceptsGraphIso
    (fused (graph core1361) (root 9) 2 0) DegreeTwoThreeSpectrum2216.graph fusedMap1361swap=true := by decide +kernel
theorem certified1361swap : Certified (graph core1361) (root 9) 2 0 :=
  of_native_maps core1361 DegreeTwoThreeSpectrum2183.graph DegreeTwoThreeSpectrum2216.graph
    sourceMap1361swap fusedMap1361swap sourceMap1361swap_checked fusedMap1361swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1361
#print axioms sourceMap1361swap_checked
#print axioms fusedMap1361swap_checked
#print axioms certified1361swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
