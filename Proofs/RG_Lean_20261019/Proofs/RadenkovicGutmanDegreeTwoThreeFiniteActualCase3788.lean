/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3788 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap3788 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3788 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3788_checked : acceptsGraphIso
    (source (graph core3788) (root 6) 1 4) DegreeTwoThreeSpectrum1951.graph sourceMap3788=true := by decide +kernel
theorem fusedMap3788_checked : acceptsGraphIso
    (fused (graph core3788) (root 6) 1 4) DegreeTwoThreeSpectrum1742.graph fusedMap3788=true := by decide +kernel
theorem certified3788 : Certified (graph core3788) (root 6) 1 4 :=
  of_native_maps core3788 DegreeTwoThreeSpectrum1951.graph DegreeTwoThreeSpectrum1742.graph
    sourceMap3788 fusedMap3788 sourceMap3788_checked fusedMap3788_checked
    DegreeTwoThreeFiniteComparisons.comparison3788
#print axioms sourceMap3788_checked
#print axioms fusedMap3788_checked
#print axioms certified3788
def sourceMap3788swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,8,9] (sourceLabel 6 4 1 v)
def fusedMap3788swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3788swap_checked : acceptsGraphIso
    (source (graph core3788) (root 6) 4 1) DegreeTwoThreeSpectrum1951.graph sourceMap3788swap=true := by decide +kernel
theorem fusedMap3788swap_checked : acceptsGraphIso
    (fused (graph core3788) (root 6) 4 1) DegreeTwoThreeSpectrum1742.graph fusedMap3788swap=true := by decide +kernel
theorem certified3788swap : Certified (graph core3788) (root 6) 4 1 :=
  of_native_maps core3788 DegreeTwoThreeSpectrum1951.graph DegreeTwoThreeSpectrum1742.graph
    sourceMap3788swap fusedMap3788swap sourceMap3788swap_checked fusedMap3788swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3788
#print axioms sourceMap3788swap_checked
#print axioms fusedMap3788swap_checked
#print axioms certified3788swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
