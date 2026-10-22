/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1340 : Family 9 := level9.get ⟨455,by decide⟩
def sourceMap1340 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1340 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1340_checked : acceptsGraphIso
    (source (graph core1340) (root 9) 0 2) DegreeTwoThreeSpectrum2136.graph sourceMap1340=true := by decide +kernel
theorem fusedMap1340_checked : acceptsGraphIso
    (fused (graph core1340) (root 9) 0 2) DegreeTwoThreeSpectrum2140.graph fusedMap1340=true := by decide +kernel
theorem certified1340 : Certified (graph core1340) (root 9) 0 2 :=
  of_native_maps core1340 DegreeTwoThreeSpectrum2136.graph DegreeTwoThreeSpectrum2140.graph
    sourceMap1340 fusedMap1340 sourceMap1340_checked fusedMap1340_checked
    DegreeTwoThreeFiniteComparisons.comparison1340
#print axioms sourceMap1340_checked
#print axioms fusedMap1340_checked
#print axioms certified1340
def sourceMap1340swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1340swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1340swap_checked : acceptsGraphIso
    (source (graph core1340) (root 9) 2 0) DegreeTwoThreeSpectrum2136.graph sourceMap1340swap=true := by decide +kernel
theorem fusedMap1340swap_checked : acceptsGraphIso
    (fused (graph core1340) (root 9) 2 0) DegreeTwoThreeSpectrum2140.graph fusedMap1340swap=true := by decide +kernel
theorem certified1340swap : Certified (graph core1340) (root 9) 2 0 :=
  of_native_maps core1340 DegreeTwoThreeSpectrum2136.graph DegreeTwoThreeSpectrum2140.graph
    sourceMap1340swap fusedMap1340swap sourceMap1340swap_checked fusedMap1340swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1340
#print axioms sourceMap1340swap_checked
#print axioms fusedMap1340swap_checked
#print axioms certified1340swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
