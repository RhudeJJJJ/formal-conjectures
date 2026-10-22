/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1493 : Family 10 := level10.get ⟨269,by decide⟩
def sourceMap1493 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1493 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1493_checked : acceptsGraphIso
    (source (graph core1493) (root 10) 0 2) DegreeTwoThreeSpectrum2620.graph sourceMap1493=true := by decide +kernel
theorem fusedMap1493_checked : acceptsGraphIso
    (fused (graph core1493) (root 10) 0 2) DegreeTwoThreeSpectrum2625.graph fusedMap1493=true := by decide +kernel
theorem certified1493 : Certified (graph core1493) (root 10) 0 2 :=
  of_native_maps core1493 DegreeTwoThreeSpectrum2620.graph DegreeTwoThreeSpectrum2625.graph
    sourceMap1493 fusedMap1493 sourceMap1493_checked fusedMap1493_checked
    DegreeTwoThreeFiniteComparisons.comparison1493
#print axioms sourceMap1493_checked
#print axioms fusedMap1493_checked
#print axioms certified1493
def sourceMap1493swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1493swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1493swap_checked : acceptsGraphIso
    (source (graph core1493) (root 10) 2 0) DegreeTwoThreeSpectrum2620.graph sourceMap1493swap=true := by decide +kernel
theorem fusedMap1493swap_checked : acceptsGraphIso
    (fused (graph core1493) (root 10) 2 0) DegreeTwoThreeSpectrum2625.graph fusedMap1493swap=true := by decide +kernel
theorem certified1493swap : Certified (graph core1493) (root 10) 2 0 :=
  of_native_maps core1493 DegreeTwoThreeSpectrum2620.graph DegreeTwoThreeSpectrum2625.graph
    sourceMap1493swap fusedMap1493swap sourceMap1493swap_checked fusedMap1493swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1493
#print axioms sourceMap1493swap_checked
#print axioms fusedMap1493swap_checked
#print axioms certified1493swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
