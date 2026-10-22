/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1287 : Family 9 := level9.get ⟨320,by decide⟩
def sourceMap1287 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1287 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1287_checked : acceptsGraphIso
    (source (graph core1287) (root 9) 0 2) DegreeTwoThreeSpectrum1930.graph sourceMap1287=true := by decide +kernel
theorem fusedMap1287_checked : acceptsGraphIso
    (fused (graph core1287) (root 9) 0 2) DegreeTwoThreeSpectrum1931.graph fusedMap1287=true := by decide +kernel
theorem certified1287 : Certified (graph core1287) (root 9) 0 2 :=
  of_native_maps core1287 DegreeTwoThreeSpectrum1930.graph DegreeTwoThreeSpectrum1931.graph
    sourceMap1287 fusedMap1287 sourceMap1287_checked fusedMap1287_checked
    DegreeTwoThreeFiniteComparisons.comparison1287
#print axioms sourceMap1287_checked
#print axioms fusedMap1287_checked
#print axioms certified1287
def sourceMap1287swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1287swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1287swap_checked : acceptsGraphIso
    (source (graph core1287) (root 9) 2 0) DegreeTwoThreeSpectrum1930.graph sourceMap1287swap=true := by decide +kernel
theorem fusedMap1287swap_checked : acceptsGraphIso
    (fused (graph core1287) (root 9) 2 0) DegreeTwoThreeSpectrum1931.graph fusedMap1287swap=true := by decide +kernel
theorem certified1287swap : Certified (graph core1287) (root 9) 2 0 :=
  of_native_maps core1287 DegreeTwoThreeSpectrum1930.graph DegreeTwoThreeSpectrum1931.graph
    sourceMap1287swap fusedMap1287swap sourceMap1287swap_checked fusedMap1287swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1287
#print axioms sourceMap1287swap_checked
#print axioms fusedMap1287swap_checked
#print axioms certified1287swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
