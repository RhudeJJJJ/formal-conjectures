/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1269 : Family 9 := level9.get ⟨273,by decide⟩
def sourceMap1269 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1269 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1269_checked : acceptsGraphIso
    (source (graph core1269) (root 9) 0 2) DegreeTwoThreeSpectrum2211.graph sourceMap1269=true := by decide +kernel
theorem fusedMap1269_checked : acceptsGraphIso
    (fused (graph core1269) (root 9) 0 2) DegreeTwoThreeSpectrum1886.graph fusedMap1269=true := by decide +kernel
theorem certified1269 : Certified (graph core1269) (root 9) 0 2 :=
  of_native_maps core1269 DegreeTwoThreeSpectrum2211.graph DegreeTwoThreeSpectrum1886.graph
    sourceMap1269 fusedMap1269 sourceMap1269_checked fusedMap1269_checked
    DegreeTwoThreeFiniteComparisons.comparison1269
#print axioms sourceMap1269_checked
#print axioms fusedMap1269_checked
#print axioms certified1269
def sourceMap1269swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1269swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1269swap_checked : acceptsGraphIso
    (source (graph core1269) (root 9) 2 0) DegreeTwoThreeSpectrum2211.graph sourceMap1269swap=true := by decide +kernel
theorem fusedMap1269swap_checked : acceptsGraphIso
    (fused (graph core1269) (root 9) 2 0) DegreeTwoThreeSpectrum1886.graph fusedMap1269swap=true := by decide +kernel
theorem certified1269swap : Certified (graph core1269) (root 9) 2 0 :=
  of_native_maps core1269 DegreeTwoThreeSpectrum2211.graph DegreeTwoThreeSpectrum1886.graph
    sourceMap1269swap fusedMap1269swap sourceMap1269swap_checked fusedMap1269swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1269
#print axioms sourceMap1269swap_checked
#print axioms fusedMap1269swap_checked
#print axioms certified1269swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
