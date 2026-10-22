/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1242 : Family 9 := level9.get ⟨193,by decide⟩
def sourceMap1242 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,10,11,12,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1242 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1242_checked : acceptsGraphIso
    (source (graph core1242) (root 9) 0 2) DegreeTwoThreeSpectrum2071.graph sourceMap1242=true := by decide +kernel
theorem fusedMap1242_checked : acceptsGraphIso
    (fused (graph core1242) (root 9) 0 2) DegreeTwoThreeSpectrum1794.graph fusedMap1242=true := by decide +kernel
theorem certified1242 : Certified (graph core1242) (root 9) 0 2 :=
  of_native_maps core1242 DegreeTwoThreeSpectrum2071.graph DegreeTwoThreeSpectrum1794.graph
    sourceMap1242 fusedMap1242 sourceMap1242_checked fusedMap1242_checked
    DegreeTwoThreeFiniteComparisons.comparison1242
#print axioms sourceMap1242_checked
#print axioms fusedMap1242_checked
#print axioms certified1242
def sourceMap1242swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,10,11,7,8,9,12] (sourceLabel 9 2 0 v)
def fusedMap1242swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1242swap_checked : acceptsGraphIso
    (source (graph core1242) (root 9) 2 0) DegreeTwoThreeSpectrum2071.graph sourceMap1242swap=true := by decide +kernel
theorem fusedMap1242swap_checked : acceptsGraphIso
    (fused (graph core1242) (root 9) 2 0) DegreeTwoThreeSpectrum1794.graph fusedMap1242swap=true := by decide +kernel
theorem certified1242swap : Certified (graph core1242) (root 9) 2 0 :=
  of_native_maps core1242 DegreeTwoThreeSpectrum2071.graph DegreeTwoThreeSpectrum1794.graph
    sourceMap1242swap fusedMap1242swap sourceMap1242swap_checked fusedMap1242swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1242
#print axioms sourceMap1242swap_checked
#print axioms fusedMap1242swap_checked
#print axioms certified1242swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
