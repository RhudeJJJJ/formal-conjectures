/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1357 : Family 9 := level9.get ⟨497,by decide⟩
def sourceMap1357 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1357 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1357_checked : acceptsGraphIso
    (source (graph core1357) (root 9) 0 2) DegreeTwoThreeSpectrum2201.graph sourceMap1357=true := by decide +kernel
theorem fusedMap1357_checked : acceptsGraphIso
    (fused (graph core1357) (root 9) 0 2) DegreeTwoThreeSpectrum2203.graph fusedMap1357=true := by decide +kernel
theorem certified1357 : Certified (graph core1357) (root 9) 0 2 :=
  of_native_maps core1357 DegreeTwoThreeSpectrum2201.graph DegreeTwoThreeSpectrum2203.graph
    sourceMap1357 fusedMap1357 sourceMap1357_checked fusedMap1357_checked
    DegreeTwoThreeFiniteComparisons.comparison1357
#print axioms sourceMap1357_checked
#print axioms fusedMap1357_checked
#print axioms certified1357
def sourceMap1357swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1357swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1357swap_checked : acceptsGraphIso
    (source (graph core1357) (root 9) 2 0) DegreeTwoThreeSpectrum2201.graph sourceMap1357swap=true := by decide +kernel
theorem fusedMap1357swap_checked : acceptsGraphIso
    (fused (graph core1357) (root 9) 2 0) DegreeTwoThreeSpectrum2203.graph fusedMap1357swap=true := by decide +kernel
theorem certified1357swap : Certified (graph core1357) (root 9) 2 0 :=
  of_native_maps core1357 DegreeTwoThreeSpectrum2201.graph DegreeTwoThreeSpectrum2203.graph
    sourceMap1357swap fusedMap1357swap sourceMap1357swap_checked fusedMap1357swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1357
#print axioms sourceMap1357swap_checked
#print axioms fusedMap1357swap_checked
#print axioms certified1357swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
