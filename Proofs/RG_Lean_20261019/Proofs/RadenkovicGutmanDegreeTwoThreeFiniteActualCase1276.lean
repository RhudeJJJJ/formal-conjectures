/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1276 : Family 9 := level9.get ⟨294,by decide⟩
def sourceMap1276 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1276 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1276_checked : acceptsGraphIso
    (source (graph core1276) (root 9) 0 2) DegreeTwoThreeSpectrum2226.graph sourceMap1276=true := by decide +kernel
theorem fusedMap1276_checked : acceptsGraphIso
    (fused (graph core1276) (root 9) 0 2) DegreeTwoThreeSpectrum1910.graph fusedMap1276=true := by decide +kernel
theorem certified1276 : Certified (graph core1276) (root 9) 0 2 :=
  of_native_maps core1276 DegreeTwoThreeSpectrum2226.graph DegreeTwoThreeSpectrum1910.graph
    sourceMap1276 fusedMap1276 sourceMap1276_checked fusedMap1276_checked
    DegreeTwoThreeFiniteComparisons.comparison1276
#print axioms sourceMap1276_checked
#print axioms fusedMap1276_checked
#print axioms certified1276
def sourceMap1276swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1276swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1276swap_checked : acceptsGraphIso
    (source (graph core1276) (root 9) 2 0) DegreeTwoThreeSpectrum2226.graph sourceMap1276swap=true := by decide +kernel
theorem fusedMap1276swap_checked : acceptsGraphIso
    (fused (graph core1276) (root 9) 2 0) DegreeTwoThreeSpectrum1910.graph fusedMap1276swap=true := by decide +kernel
theorem certified1276swap : Certified (graph core1276) (root 9) 2 0 :=
  of_native_maps core1276 DegreeTwoThreeSpectrum2226.graph DegreeTwoThreeSpectrum1910.graph
    sourceMap1276swap fusedMap1276swap sourceMap1276swap_checked fusedMap1276swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1276
#print axioms sourceMap1276swap_checked
#print axioms fusedMap1276swap_checked
#print axioms certified1276swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
