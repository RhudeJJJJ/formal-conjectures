/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3114 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap3114 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3114 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3114_checked : acceptsGraphIso
    (source (graph core3114) (root 7) 0 5) DegreeTwoThreeSpectrum2719.graph sourceMap3114=true := by decide +kernel
theorem fusedMap3114_checked : acceptsGraphIso
    (fused (graph core3114) (root 7) 0 5) DegreeTwoThreeSpectrum2356.graph fusedMap3114=true := by decide +kernel
theorem certified3114 : Certified (graph core3114) (root 7) 0 5 :=
  of_native_maps core3114 DegreeTwoThreeSpectrum2719.graph DegreeTwoThreeSpectrum2356.graph
    sourceMap3114 fusedMap3114 sourceMap3114_checked fusedMap3114_checked
    DegreeTwoThreeFiniteComparisons.comparison3114
#print axioms sourceMap3114_checked
#print axioms fusedMap3114_checked
#print axioms certified3114
def sourceMap3114swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3114swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3114swap_checked : acceptsGraphIso
    (source (graph core3114) (root 7) 5 0) DegreeTwoThreeSpectrum2719.graph sourceMap3114swap=true := by decide +kernel
theorem fusedMap3114swap_checked : acceptsGraphIso
    (fused (graph core3114) (root 7) 5 0) DegreeTwoThreeSpectrum2356.graph fusedMap3114swap=true := by decide +kernel
theorem certified3114swap : Certified (graph core3114) (root 7) 5 0 :=
  of_native_maps core3114 DegreeTwoThreeSpectrum2719.graph DegreeTwoThreeSpectrum2356.graph
    sourceMap3114swap fusedMap3114swap sourceMap3114swap_checked fusedMap3114swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3114
#print axioms sourceMap3114swap_checked
#print axioms fusedMap3114swap_checked
#print axioms certified3114swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
