/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3549 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap3549 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3549 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3549_checked : acceptsGraphIso
    (source (graph core3549) (root 8) 0 6) DegreeTwoThreeSpectrum5389.graph sourceMap3549=true := by decide +kernel
theorem fusedMap3549_checked : acceptsGraphIso
    (fused (graph core3549) (root 8) 0 6) DegreeTwoThreeSpectrum4990.graph fusedMap3549=true := by decide +kernel
theorem certified3549 : Certified (graph core3549) (root 8) 0 6 :=
  of_native_maps core3549 DegreeTwoThreeSpectrum5389.graph DegreeTwoThreeSpectrum4990.graph
    sourceMap3549 fusedMap3549 sourceMap3549_checked fusedMap3549_checked
    DegreeTwoThreeFiniteComparisons.comparison3549
#print axioms sourceMap3549_checked
#print axioms fusedMap3549_checked
#print axioms certified3549
def sourceMap3549swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3549swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3549swap_checked : acceptsGraphIso
    (source (graph core3549) (root 8) 6 0) DegreeTwoThreeSpectrum5389.graph sourceMap3549swap=true := by decide +kernel
theorem fusedMap3549swap_checked : acceptsGraphIso
    (fused (graph core3549) (root 8) 6 0) DegreeTwoThreeSpectrum4990.graph fusedMap3549swap=true := by decide +kernel
theorem certified3549swap : Certified (graph core3549) (root 8) 6 0 :=
  of_native_maps core3549 DegreeTwoThreeSpectrum5389.graph DegreeTwoThreeSpectrum4990.graph
    sourceMap3549swap fusedMap3549swap sourceMap3549swap_checked fusedMap3549swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3549
#print axioms sourceMap3549swap_checked
#print axioms fusedMap3549swap_checked
#print axioms certified3549swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
