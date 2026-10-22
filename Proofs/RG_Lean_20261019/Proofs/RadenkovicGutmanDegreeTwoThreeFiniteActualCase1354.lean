/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1354 : Family 9 := level9.get ⟨489,by decide⟩
def sourceMap1354 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1354 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1354_checked : acceptsGraphIso
    (source (graph core1354) (root 9) 0 2) DegreeTwoThreeSpectrum2187.graph sourceMap1354=true := by decide +kernel
theorem fusedMap1354_checked : acceptsGraphIso
    (fused (graph core1354) (root 9) 0 2) DegreeTwoThreeSpectrum2189.graph fusedMap1354=true := by decide +kernel
theorem certified1354 : Certified (graph core1354) (root 9) 0 2 :=
  of_native_maps core1354 DegreeTwoThreeSpectrum2187.graph DegreeTwoThreeSpectrum2189.graph
    sourceMap1354 fusedMap1354 sourceMap1354_checked fusedMap1354_checked
    DegreeTwoThreeFiniteComparisons.comparison1354
#print axioms sourceMap1354_checked
#print axioms fusedMap1354_checked
#print axioms certified1354
def sourceMap1354swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1354swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1354swap_checked : acceptsGraphIso
    (source (graph core1354) (root 9) 2 0) DegreeTwoThreeSpectrum2187.graph sourceMap1354swap=true := by decide +kernel
theorem fusedMap1354swap_checked : acceptsGraphIso
    (fused (graph core1354) (root 9) 2 0) DegreeTwoThreeSpectrum2189.graph fusedMap1354swap=true := by decide +kernel
theorem certified1354swap : Certified (graph core1354) (root 9) 2 0 :=
  of_native_maps core1354 DegreeTwoThreeSpectrum2187.graph DegreeTwoThreeSpectrum2189.graph
    sourceMap1354swap fusedMap1354swap sourceMap1354swap_checked fusedMap1354swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1354
#print axioms sourceMap1354swap_checked
#print axioms fusedMap1354swap_checked
#print axioms certified1354swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
