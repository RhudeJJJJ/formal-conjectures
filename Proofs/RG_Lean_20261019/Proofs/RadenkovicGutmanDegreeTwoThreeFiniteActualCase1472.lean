/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1472 : Family 10 := level10.get ⟨185,by decide⟩
def sourceMap1472 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1472 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1472_checked : acceptsGraphIso
    (source (graph core1472) (root 10) 0 2) DegreeTwoThreeSpectrum2819.graph sourceMap1472=true := by decide +kernel
theorem fusedMap1472_checked : acceptsGraphIso
    (fused (graph core1472) (root 10) 0 2) DegreeTwoThreeSpectrum2408.graph fusedMap1472=true := by decide +kernel
theorem certified1472 : Certified (graph core1472) (root 10) 0 2 :=
  of_native_maps core1472 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2408.graph
    sourceMap1472 fusedMap1472 sourceMap1472_checked fusedMap1472_checked
    DegreeTwoThreeFiniteComparisons.comparison1472
#print axioms sourceMap1472_checked
#print axioms fusedMap1472_checked
#print axioms certified1472
def sourceMap1472swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1472swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1472swap_checked : acceptsGraphIso
    (source (graph core1472) (root 10) 2 0) DegreeTwoThreeSpectrum2819.graph sourceMap1472swap=true := by decide +kernel
theorem fusedMap1472swap_checked : acceptsGraphIso
    (fused (graph core1472) (root 10) 2 0) DegreeTwoThreeSpectrum2408.graph fusedMap1472swap=true := by decide +kernel
theorem certified1472swap : Certified (graph core1472) (root 10) 2 0 :=
  of_native_maps core1472 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2408.graph
    sourceMap1472swap fusedMap1472swap sourceMap1472swap_checked fusedMap1472swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1472
#print axioms sourceMap1472swap_checked
#print axioms fusedMap1472swap_checked
#print axioms certified1472swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
