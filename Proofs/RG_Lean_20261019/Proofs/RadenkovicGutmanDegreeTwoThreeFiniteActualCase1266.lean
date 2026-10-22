/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1266 : Family 9 := level9.get ⟨265,by decide⟩
def sourceMap1266 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1266 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1266_checked : acceptsGraphIso
    (source (graph core1266) (root 9) 0 2) DegreeTwoThreeSpectrum2209.graph sourceMap1266=true := by decide +kernel
theorem fusedMap1266_checked : acceptsGraphIso
    (fused (graph core1266) (root 9) 0 2) DegreeTwoThreeSpectrum1875.graph fusedMap1266=true := by decide +kernel
theorem certified1266 : Certified (graph core1266) (root 9) 0 2 :=
  of_native_maps core1266 DegreeTwoThreeSpectrum2209.graph DegreeTwoThreeSpectrum1875.graph
    sourceMap1266 fusedMap1266 sourceMap1266_checked fusedMap1266_checked
    DegreeTwoThreeFiniteComparisons.comparison1266
#print axioms sourceMap1266_checked
#print axioms fusedMap1266_checked
#print axioms certified1266
def sourceMap1266swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1266swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1266swap_checked : acceptsGraphIso
    (source (graph core1266) (root 9) 2 0) DegreeTwoThreeSpectrum2209.graph sourceMap1266swap=true := by decide +kernel
theorem fusedMap1266swap_checked : acceptsGraphIso
    (fused (graph core1266) (root 9) 2 0) DegreeTwoThreeSpectrum1875.graph fusedMap1266swap=true := by decide +kernel
theorem certified1266swap : Certified (graph core1266) (root 9) 2 0 :=
  of_native_maps core1266 DegreeTwoThreeSpectrum2209.graph DegreeTwoThreeSpectrum1875.graph
    sourceMap1266swap fusedMap1266swap sourceMap1266swap_checked fusedMap1266swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1266
#print axioms sourceMap1266swap_checked
#print axioms fusedMap1266swap_checked
#print axioms certified1266swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
