/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1480 : Family 10 := level10.get ⟨220,by decide⟩
def sourceMap1480 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1480 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1480_checked : acceptsGraphIso
    (source (graph core1480) (root 10) 0 2) DegreeTwoThreeSpectrum2517.graph sourceMap1480=true := by decide +kernel
theorem fusedMap1480_checked : acceptsGraphIso
    (fused (graph core1480) (root 10) 0 2) DegreeTwoThreeSpectrum2519.graph fusedMap1480=true := by decide +kernel
theorem certified1480 : Certified (graph core1480) (root 10) 0 2 :=
  of_native_maps core1480 DegreeTwoThreeSpectrum2517.graph DegreeTwoThreeSpectrum2519.graph
    sourceMap1480 fusedMap1480 sourceMap1480_checked fusedMap1480_checked
    DegreeTwoThreeFiniteComparisons.comparison1480
#print axioms sourceMap1480_checked
#print axioms fusedMap1480_checked
#print axioms certified1480
def sourceMap1480swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1480swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1480swap_checked : acceptsGraphIso
    (source (graph core1480) (root 10) 2 0) DegreeTwoThreeSpectrum2517.graph sourceMap1480swap=true := by decide +kernel
theorem fusedMap1480swap_checked : acceptsGraphIso
    (fused (graph core1480) (root 10) 2 0) DegreeTwoThreeSpectrum2519.graph fusedMap1480swap=true := by decide +kernel
theorem certified1480swap : Certified (graph core1480) (root 10) 2 0 :=
  of_native_maps core1480 DegreeTwoThreeSpectrum2517.graph DegreeTwoThreeSpectrum2519.graph
    sourceMap1480swap fusedMap1480swap sourceMap1480swap_checked fusedMap1480swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1480
#print axioms sourceMap1480swap_checked
#print axioms fusedMap1480swap_checked
#print axioms certified1480swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
