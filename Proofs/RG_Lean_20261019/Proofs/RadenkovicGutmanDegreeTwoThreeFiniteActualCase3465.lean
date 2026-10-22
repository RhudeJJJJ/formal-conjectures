/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3465 : Family 9 := level9.get ⟨653,by decide⟩
def sourceMap3465 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3465 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3465_checked : acceptsGraphIso
    (source (graph core3465) (root 9) 0 5) DegreeTwoThreeSpectrum6598.graph sourceMap3465=true := by decide +kernel
theorem fusedMap3465_checked : acceptsGraphIso
    (fused (graph core3465) (root 9) 0 5) DegreeTwoThreeSpectrum6599.graph fusedMap3465=true := by decide +kernel
theorem certified3465 : Certified (graph core3465) (root 9) 0 5 :=
  of_native_maps core3465 DegreeTwoThreeSpectrum6598.graph DegreeTwoThreeSpectrum6599.graph
    sourceMap3465 fusedMap3465 sourceMap3465_checked fusedMap3465_checked
    DegreeTwoThreeFiniteComparisons.comparison3465
#print axioms sourceMap3465_checked
#print axioms fusedMap3465_checked
#print axioms certified3465
def sourceMap3465swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3465swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3465swap_checked : acceptsGraphIso
    (source (graph core3465) (root 9) 5 0) DegreeTwoThreeSpectrum6598.graph sourceMap3465swap=true := by decide +kernel
theorem fusedMap3465swap_checked : acceptsGraphIso
    (fused (graph core3465) (root 9) 5 0) DegreeTwoThreeSpectrum6599.graph fusedMap3465swap=true := by decide +kernel
theorem certified3465swap : Certified (graph core3465) (root 9) 5 0 :=
  of_native_maps core3465 DegreeTwoThreeSpectrum6598.graph DegreeTwoThreeSpectrum6599.graph
    sourceMap3465swap fusedMap3465swap sourceMap3465swap_checked fusedMap3465swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3465
#print axioms sourceMap3465swap_checked
#print axioms fusedMap3465swap_checked
#print axioms certified3465swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
