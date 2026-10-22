/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1246 : Family 9 := level9.get ⟨207,by decide⟩
def sourceMap1246 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1246 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1246_checked : acceptsGraphIso
    (source (graph core1246) (root 9) 0 2) DegreeTwoThreeSpectrum2104.graph sourceMap1246=true := by decide +kernel
theorem fusedMap1246_checked : acceptsGraphIso
    (fused (graph core1246) (root 9) 0 2) DegreeTwoThreeSpectrum1810.graph fusedMap1246=true := by decide +kernel
theorem certified1246 : Certified (graph core1246) (root 9) 0 2 :=
  of_native_maps core1246 DegreeTwoThreeSpectrum2104.graph DegreeTwoThreeSpectrum1810.graph
    sourceMap1246 fusedMap1246 sourceMap1246_checked fusedMap1246_checked
    DegreeTwoThreeFiniteComparisons.comparison1246
#print axioms sourceMap1246_checked
#print axioms fusedMap1246_checked
#print axioms certified1246
def sourceMap1246swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1246swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1246swap_checked : acceptsGraphIso
    (source (graph core1246) (root 9) 2 0) DegreeTwoThreeSpectrum2104.graph sourceMap1246swap=true := by decide +kernel
theorem fusedMap1246swap_checked : acceptsGraphIso
    (fused (graph core1246) (root 9) 2 0) DegreeTwoThreeSpectrum1810.graph fusedMap1246swap=true := by decide +kernel
theorem certified1246swap : Certified (graph core1246) (root 9) 2 0 :=
  of_native_maps core1246 DegreeTwoThreeSpectrum2104.graph DegreeTwoThreeSpectrum1810.graph
    sourceMap1246swap fusedMap1246swap sourceMap1246swap_checked fusedMap1246swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1246
#print axioms sourceMap1246swap_checked
#print axioms fusedMap1246swap_checked
#print axioms certified1246swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
