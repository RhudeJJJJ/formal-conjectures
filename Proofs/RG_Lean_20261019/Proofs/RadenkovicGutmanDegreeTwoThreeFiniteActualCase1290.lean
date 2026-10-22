/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1290 : Family 9 := level9.get ⟨328,by decide⟩
def sourceMap1290 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1290 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1290_checked : acceptsGraphIso
    (source (graph core1290) (root 9) 0 2) DegreeTwoThreeSpectrum1945.graph sourceMap1290=true := by decide +kernel
theorem fusedMap1290_checked : acceptsGraphIso
    (fused (graph core1290) (root 9) 0 2) DegreeTwoThreeSpectrum1947.graph fusedMap1290=true := by decide +kernel
theorem certified1290 : Certified (graph core1290) (root 9) 0 2 :=
  of_native_maps core1290 DegreeTwoThreeSpectrum1945.graph DegreeTwoThreeSpectrum1947.graph
    sourceMap1290 fusedMap1290 sourceMap1290_checked fusedMap1290_checked
    DegreeTwoThreeFiniteComparisons.comparison1290
#print axioms sourceMap1290_checked
#print axioms fusedMap1290_checked
#print axioms certified1290
def sourceMap1290swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1290swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1290swap_checked : acceptsGraphIso
    (source (graph core1290) (root 9) 2 0) DegreeTwoThreeSpectrum1945.graph sourceMap1290swap=true := by decide +kernel
theorem fusedMap1290swap_checked : acceptsGraphIso
    (fused (graph core1290) (root 9) 2 0) DegreeTwoThreeSpectrum1947.graph fusedMap1290swap=true := by decide +kernel
theorem certified1290swap : Certified (graph core1290) (root 9) 2 0 :=
  of_native_maps core1290 DegreeTwoThreeSpectrum1945.graph DegreeTwoThreeSpectrum1947.graph
    sourceMap1290swap fusedMap1290swap sourceMap1290swap_checked fusedMap1290swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1290
#print axioms sourceMap1290swap_checked
#print axioms fusedMap1290swap_checked
#print axioms certified1290swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
