/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1551 : Family 10 := level10.get ⟨458,by decide⟩
def sourceMap1551 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1551 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1551_checked : acceptsGraphIso
    (source (graph core1551) (root 10) 0 2) DegreeTwoThreeSpectrum2883.graph sourceMap1551=true := by decide +kernel
theorem fusedMap1551_checked : acceptsGraphIso
    (fused (graph core1551) (root 10) 0 2) DegreeTwoThreeSpectrum2987.graph fusedMap1551=true := by decide +kernel
theorem certified1551 : Certified (graph core1551) (root 10) 0 2 :=
  of_native_maps core1551 DegreeTwoThreeSpectrum2883.graph DegreeTwoThreeSpectrum2987.graph
    sourceMap1551 fusedMap1551 sourceMap1551_checked fusedMap1551_checked
    DegreeTwoThreeFiniteComparisons.comparison1551
#print axioms sourceMap1551_checked
#print axioms fusedMap1551_checked
#print axioms certified1551
def sourceMap1551swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1551swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1551swap_checked : acceptsGraphIso
    (source (graph core1551) (root 10) 2 0) DegreeTwoThreeSpectrum2883.graph sourceMap1551swap=true := by decide +kernel
theorem fusedMap1551swap_checked : acceptsGraphIso
    (fused (graph core1551) (root 10) 2 0) DegreeTwoThreeSpectrum2987.graph fusedMap1551swap=true := by decide +kernel
theorem certified1551swap : Certified (graph core1551) (root 10) 2 0 :=
  of_native_maps core1551 DegreeTwoThreeSpectrum2883.graph DegreeTwoThreeSpectrum2987.graph
    sourceMap1551swap fusedMap1551swap sourceMap1551swap_checked fusedMap1551swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1551
#print axioms sourceMap1551swap_checked
#print axioms fusedMap1551swap_checked
#print axioms certified1551swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
