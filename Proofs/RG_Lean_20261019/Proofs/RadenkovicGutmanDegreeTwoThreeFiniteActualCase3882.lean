/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3882 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap3882 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3882 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3882_checked : acceptsGraphIso
    (source (graph core3882) (root 8) 1 4) DegreeTwoThreeSpectrum4603.graph sourceMap3882=true := by decide +kernel
theorem fusedMap3882_checked : acceptsGraphIso
    (fused (graph core3882) (root 8) 1 4) DegreeTwoThreeSpectrum4083.graph fusedMap3882=true := by decide +kernel
theorem certified3882 : Certified (graph core3882) (root 8) 1 4 :=
  of_native_maps core3882 DegreeTwoThreeSpectrum4603.graph DegreeTwoThreeSpectrum4083.graph
    sourceMap3882 fusedMap3882 sourceMap3882_checked fusedMap3882_checked
    DegreeTwoThreeFiniteComparisons.comparison3882
#print axioms sourceMap3882_checked
#print axioms fusedMap3882_checked
#print axioms certified3882
def sourceMap3882swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3882swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3882swap_checked : acceptsGraphIso
    (source (graph core3882) (root 8) 4 1) DegreeTwoThreeSpectrum4603.graph sourceMap3882swap=true := by decide +kernel
theorem fusedMap3882swap_checked : acceptsGraphIso
    (fused (graph core3882) (root 8) 4 1) DegreeTwoThreeSpectrum4083.graph fusedMap3882swap=true := by decide +kernel
theorem certified3882swap : Certified (graph core3882) (root 8) 4 1 :=
  of_native_maps core3882 DegreeTwoThreeSpectrum4603.graph DegreeTwoThreeSpectrum4083.graph
    sourceMap3882swap fusedMap3882swap sourceMap3882swap_checked fusedMap3882swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3882
#print axioms sourceMap3882swap_checked
#print axioms fusedMap3882swap_checked
#print axioms certified3882swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
