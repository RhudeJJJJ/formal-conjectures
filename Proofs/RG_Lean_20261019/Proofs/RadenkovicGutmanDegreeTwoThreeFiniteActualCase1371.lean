/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1371 : Family 9 := level9.get ⟨527,by decide⟩
def sourceMap1371 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,9,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1371 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 0 2 v)
theorem sourceMap1371_checked : acceptsGraphIso
    (source (graph core1371) (root 9) 0 2) DegreeTwoThreeSpectrum1971.graph sourceMap1371=true := by decide +kernel
theorem fusedMap1371_checked : acceptsGraphIso
    (fused (graph core1371) (root 9) 0 2) DegreeTwoThreeSpectrum2234.graph fusedMap1371=true := by decide +kernel
theorem certified1371 : Certified (graph core1371) (root 9) 0 2 :=
  of_native_maps core1371 DegreeTwoThreeSpectrum1971.graph DegreeTwoThreeSpectrum2234.graph
    sourceMap1371 fusedMap1371 sourceMap1371_checked fusedMap1371_checked
    DegreeTwoThreeFiniteComparisons.comparison1371
#print axioms sourceMap1371_checked
#print axioms fusedMap1371_checked
#print axioms certified1371
def sourceMap1371swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,6,7,8,9] (sourceLabel 9 2 0 v)
def fusedMap1371swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 2 0 v)
theorem sourceMap1371swap_checked : acceptsGraphIso
    (source (graph core1371) (root 9) 2 0) DegreeTwoThreeSpectrum1971.graph sourceMap1371swap=true := by decide +kernel
theorem fusedMap1371swap_checked : acceptsGraphIso
    (fused (graph core1371) (root 9) 2 0) DegreeTwoThreeSpectrum2234.graph fusedMap1371swap=true := by decide +kernel
theorem certified1371swap : Certified (graph core1371) (root 9) 2 0 :=
  of_native_maps core1371 DegreeTwoThreeSpectrum1971.graph DegreeTwoThreeSpectrum2234.graph
    sourceMap1371swap fusedMap1371swap sourceMap1371swap_checked fusedMap1371swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1371
#print axioms sourceMap1371swap_checked
#print axioms fusedMap1371swap_checked
#print axioms certified1371swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
