/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1291 : Family 9 := level9.get ⟨333,by decide⟩
def sourceMap1291 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1291 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1291_checked : acceptsGraphIso
    (source (graph core1291) (root 9) 0 2) DegreeTwoThreeSpectrum1955.graph sourceMap1291=true := by decide +kernel
theorem fusedMap1291_checked : acceptsGraphIso
    (fused (graph core1291) (root 9) 0 2) DegreeTwoThreeSpectrum1956.graph fusedMap1291=true := by decide +kernel
theorem certified1291 : Certified (graph core1291) (root 9) 0 2 :=
  of_native_maps core1291 DegreeTwoThreeSpectrum1955.graph DegreeTwoThreeSpectrum1956.graph
    sourceMap1291 fusedMap1291 sourceMap1291_checked fusedMap1291_checked
    DegreeTwoThreeFiniteComparisons.comparison1291
#print axioms sourceMap1291_checked
#print axioms fusedMap1291_checked
#print axioms certified1291
def sourceMap1291swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1291swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1291swap_checked : acceptsGraphIso
    (source (graph core1291) (root 9) 2 0) DegreeTwoThreeSpectrum1955.graph sourceMap1291swap=true := by decide +kernel
theorem fusedMap1291swap_checked : acceptsGraphIso
    (fused (graph core1291) (root 9) 2 0) DegreeTwoThreeSpectrum1956.graph fusedMap1291swap=true := by decide +kernel
theorem certified1291swap : Certified (graph core1291) (root 9) 2 0 :=
  of_native_maps core1291 DegreeTwoThreeSpectrum1955.graph DegreeTwoThreeSpectrum1956.graph
    sourceMap1291swap fusedMap1291swap sourceMap1291swap_checked fusedMap1291swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1291
#print axioms sourceMap1291swap_checked
#print axioms fusedMap1291swap_checked
#print axioms certified1291swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
