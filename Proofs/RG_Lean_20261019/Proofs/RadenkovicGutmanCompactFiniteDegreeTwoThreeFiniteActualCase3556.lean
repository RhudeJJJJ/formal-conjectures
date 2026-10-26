/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3556 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap3556 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3556 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3556_checked : acceptsGraphIso
    (source (graph core3556) (root 8) 0 6) DegreeTwoThreeSpectrum5719.graph sourceMap3556=true := by decide +kernel
theorem fusedMap3556_checked : acceptsGraphIso
    (fused (graph core3556) (root 8) 0 6) DegreeTwoThreeSpectrum5052.graph fusedMap3556=true := by decide +kernel
theorem certified3556 : Certified (graph core3556) (root 8) 0 6 :=
  of_native_maps core3556 DegreeTwoThreeSpectrum5719.graph DegreeTwoThreeSpectrum5052.graph
    sourceMap3556 fusedMap3556 sourceMap3556_checked fusedMap3556_checked
    DegreeTwoThreeFiniteComparisons.comparison3556
#print axioms sourceMap3556_checked
#print axioms fusedMap3556_checked
#print axioms certified3556
def sourceMap3556swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3556swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3556swap_checked : acceptsGraphIso
    (source (graph core3556) (root 8) 6 0) DegreeTwoThreeSpectrum5719.graph sourceMap3556swap=true := by decide +kernel
theorem fusedMap3556swap_checked : acceptsGraphIso
    (fused (graph core3556) (root 8) 6 0) DegreeTwoThreeSpectrum5052.graph fusedMap3556swap=true := by decide +kernel
theorem certified3556swap : Certified (graph core3556) (root 8) 6 0 :=
  of_native_maps core3556 DegreeTwoThreeSpectrum5719.graph DegreeTwoThreeSpectrum5052.graph
    sourceMap3556swap fusedMap3556swap sourceMap3556swap_checked fusedMap3556swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3556
#print axioms sourceMap3556swap_checked
#print axioms fusedMap3556swap_checked
#print axioms certified3556swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
