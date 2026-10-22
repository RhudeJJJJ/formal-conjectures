/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1220 : Family 9 := level9.get ⟨123,by decide⟩
def sourceMap1220 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1220 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,6,7,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1220_checked : acceptsGraphIso
    (source (graph core1220) (root 9) 0 2) DegreeTwoThreeSpectrum1869.graph sourceMap1220=true := by decide +kernel
theorem fusedMap1220_checked : acceptsGraphIso
    (fused (graph core1220) (root 9) 0 2) DegreeTwoThreeSpectrum1917.graph fusedMap1220=true := by decide +kernel
theorem certified1220 : Certified (graph core1220) (root 9) 0 2 :=
  of_native_maps core1220 DegreeTwoThreeSpectrum1869.graph DegreeTwoThreeSpectrum1917.graph
    sourceMap1220 fusedMap1220 sourceMap1220_checked fusedMap1220_checked
    DegreeTwoThreeFiniteComparisons.comparison1220
#print axioms sourceMap1220_checked
#print axioms fusedMap1220_checked
#print axioms certified1220
def sourceMap1220swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1220swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,6,7,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1220swap_checked : acceptsGraphIso
    (source (graph core1220) (root 9) 2 0) DegreeTwoThreeSpectrum1869.graph sourceMap1220swap=true := by decide +kernel
theorem fusedMap1220swap_checked : acceptsGraphIso
    (fused (graph core1220) (root 9) 2 0) DegreeTwoThreeSpectrum1917.graph fusedMap1220swap=true := by decide +kernel
theorem certified1220swap : Certified (graph core1220) (root 9) 2 0 :=
  of_native_maps core1220 DegreeTwoThreeSpectrum1869.graph DegreeTwoThreeSpectrum1917.graph
    sourceMap1220swap fusedMap1220swap sourceMap1220swap_checked fusedMap1220swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1220
#print axioms sourceMap1220swap_checked
#print axioms fusedMap1220swap_checked
#print axioms certified1220swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
