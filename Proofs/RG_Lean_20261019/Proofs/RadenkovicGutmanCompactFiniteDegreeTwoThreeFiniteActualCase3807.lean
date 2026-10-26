/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3807 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap3807 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3807 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3807_checked : acceptsGraphIso
    (source (graph core3807) (root 7) 1 4) DegreeTwoThreeSpectrum2954.graph sourceMap3807=true := by decide +kernel
theorem fusedMap3807_checked : acceptsGraphIso
    (fused (graph core3807) (root 7) 1 4) DegreeTwoThreeSpectrum2408.graph fusedMap3807=true := by decide +kernel
theorem certified3807 : Certified (graph core3807) (root 7) 1 4 :=
  of_native_maps core3807 DegreeTwoThreeSpectrum2954.graph DegreeTwoThreeSpectrum2408.graph
    sourceMap3807 fusedMap3807 sourceMap3807_checked fusedMap3807_checked
    DegreeTwoThreeFiniteComparisons.comparison3807
#print axioms sourceMap3807_checked
#print axioms fusedMap3807_checked
#print axioms certified3807
def sourceMap3807swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3807swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3807swap_checked : acceptsGraphIso
    (source (graph core3807) (root 7) 4 1) DegreeTwoThreeSpectrum2954.graph sourceMap3807swap=true := by decide +kernel
theorem fusedMap3807swap_checked : acceptsGraphIso
    (fused (graph core3807) (root 7) 4 1) DegreeTwoThreeSpectrum2408.graph fusedMap3807swap=true := by decide +kernel
theorem certified3807swap : Certified (graph core3807) (root 7) 4 1 :=
  of_native_maps core3807 DegreeTwoThreeSpectrum2954.graph DegreeTwoThreeSpectrum2408.graph
    sourceMap3807swap fusedMap3807swap sourceMap3807swap_checked fusedMap3807swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3807
#print axioms sourceMap3807swap_checked
#print axioms fusedMap3807swap_checked
#print axioms certified3807swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
