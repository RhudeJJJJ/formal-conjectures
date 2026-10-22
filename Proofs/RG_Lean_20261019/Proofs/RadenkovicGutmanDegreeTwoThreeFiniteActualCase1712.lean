/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1712 : Family 10 := level10.get ⟨912,by decide⟩
def sourceMap1712 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1712 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1712_checked : acceptsGraphIso
    (source (graph core1712) (root 10) 0 2) DegreeTwoThreeSpectrum3627.graph sourceMap1712=true := by decide +kernel
theorem fusedMap1712_checked : acceptsGraphIso
    (fused (graph core1712) (root 10) 0 2) DegreeTwoThreeSpectrum2925.graph fusedMap1712=true := by decide +kernel
theorem certified1712 : Certified (graph core1712) (root 10) 0 2 :=
  of_native_maps core1712 DegreeTwoThreeSpectrum3627.graph DegreeTwoThreeSpectrum2925.graph
    sourceMap1712 fusedMap1712 sourceMap1712_checked fusedMap1712_checked
    DegreeTwoThreeFiniteComparisons.comparison1712
#print axioms sourceMap1712_checked
#print axioms fusedMap1712_checked
#print axioms certified1712
def sourceMap1712swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1712swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1712swap_checked : acceptsGraphIso
    (source (graph core1712) (root 10) 2 0) DegreeTwoThreeSpectrum3627.graph sourceMap1712swap=true := by decide +kernel
theorem fusedMap1712swap_checked : acceptsGraphIso
    (fused (graph core1712) (root 10) 2 0) DegreeTwoThreeSpectrum2925.graph fusedMap1712swap=true := by decide +kernel
theorem certified1712swap : Certified (graph core1712) (root 10) 2 0 :=
  of_native_maps core1712 DegreeTwoThreeSpectrum3627.graph DegreeTwoThreeSpectrum2925.graph
    sourceMap1712swap fusedMap1712swap sourceMap1712swap_checked fusedMap1712swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1712
#print axioms sourceMap1712swap_checked
#print axioms fusedMap1712swap_checked
#print axioms certified1712swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
