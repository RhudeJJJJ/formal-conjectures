/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1465 : Family 10 := level10.get ⟨168,by decide⟩
def sourceMap1465 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1465 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1465_checked : acceptsGraphIso
    (source (graph core1465) (root 10) 0 2) DegreeTwoThreeSpectrum2908.graph sourceMap1465=true := by decide +kernel
theorem fusedMap1465_checked : acceptsGraphIso
    (fused (graph core1465) (root 10) 0 2) DegreeTwoThreeSpectrum2424.graph fusedMap1465=true := by decide +kernel
theorem certified1465 : Certified (graph core1465) (root 10) 0 2 :=
  of_native_maps core1465 DegreeTwoThreeSpectrum2908.graph DegreeTwoThreeSpectrum2424.graph
    sourceMap1465 fusedMap1465 sourceMap1465_checked fusedMap1465_checked
    DegreeTwoThreeFiniteComparisons.comparison1465
#print axioms sourceMap1465_checked
#print axioms fusedMap1465_checked
#print axioms certified1465
def sourceMap1465swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1465swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1465swap_checked : acceptsGraphIso
    (source (graph core1465) (root 10) 2 0) DegreeTwoThreeSpectrum2908.graph sourceMap1465swap=true := by decide +kernel
theorem fusedMap1465swap_checked : acceptsGraphIso
    (fused (graph core1465) (root 10) 2 0) DegreeTwoThreeSpectrum2424.graph fusedMap1465swap=true := by decide +kernel
theorem certified1465swap : Certified (graph core1465) (root 10) 2 0 :=
  of_native_maps core1465 DegreeTwoThreeSpectrum2908.graph DegreeTwoThreeSpectrum2424.graph
    sourceMap1465swap fusedMap1465swap sourceMap1465swap_checked fusedMap1465swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1465
#print axioms sourceMap1465swap_checked
#print axioms fusedMap1465swap_checked
#print axioms certified1465swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
