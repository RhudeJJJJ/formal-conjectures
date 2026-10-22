/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3112 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap3112 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3112 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3112_checked : acceptsGraphIso
    (source (graph core3112) (root 7) 0 5) DegreeTwoThreeSpectrum2611.graph sourceMap3112=true := by decide +kernel
theorem fusedMap3112_checked : acceptsGraphIso
    (fused (graph core3112) (root 7) 0 5) DegreeTwoThreeSpectrum2334.graph fusedMap3112=true := by decide +kernel
theorem certified3112 : Certified (graph core3112) (root 7) 0 5 :=
  of_native_maps core3112 DegreeTwoThreeSpectrum2611.graph DegreeTwoThreeSpectrum2334.graph
    sourceMap3112 fusedMap3112 sourceMap3112_checked fusedMap3112_checked
    DegreeTwoThreeFiniteComparisons.comparison3112
#print axioms sourceMap3112_checked
#print axioms fusedMap3112_checked
#print axioms certified3112
def sourceMap3112swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3112swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3112swap_checked : acceptsGraphIso
    (source (graph core3112) (root 7) 5 0) DegreeTwoThreeSpectrum2611.graph sourceMap3112swap=true := by decide +kernel
theorem fusedMap3112swap_checked : acceptsGraphIso
    (fused (graph core3112) (root 7) 5 0) DegreeTwoThreeSpectrum2334.graph fusedMap3112swap=true := by decide +kernel
theorem certified3112swap : Certified (graph core3112) (root 7) 5 0 :=
  of_native_maps core3112 DegreeTwoThreeSpectrum2611.graph DegreeTwoThreeSpectrum2334.graph
    sourceMap3112swap fusedMap3112swap sourceMap3112swap_checked fusedMap3112swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3112
#print axioms sourceMap3112swap_checked
#print axioms fusedMap3112swap_checked
#print axioms certified3112swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
