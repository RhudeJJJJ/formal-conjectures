/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3593 : Family 8 := level8.get ⟨172,by decide⟩
def sourceMap3593 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3593 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3593_checked : acceptsGraphIso
    (source (graph core3593) (root 8) 0 6) DegreeTwoThreeSpectrum5729.graph sourceMap3593=true := by decide +kernel
theorem fusedMap3593_checked : acceptsGraphIso
    (fused (graph core3593) (root 8) 0 6) DegreeTwoThreeSpectrum5731.graph fusedMap3593=true := by decide +kernel
theorem certified3593 : Certified (graph core3593) (root 8) 0 6 :=
  of_native_maps core3593 DegreeTwoThreeSpectrum5729.graph DegreeTwoThreeSpectrum5731.graph
    sourceMap3593 fusedMap3593 sourceMap3593_checked fusedMap3593_checked
    DegreeTwoThreeFiniteComparisons.comparison3593
#print axioms sourceMap3593_checked
#print axioms fusedMap3593_checked
#print axioms certified3593
def sourceMap3593swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3593swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3593swap_checked : acceptsGraphIso
    (source (graph core3593) (root 8) 6 0) DegreeTwoThreeSpectrum5729.graph sourceMap3593swap=true := by decide +kernel
theorem fusedMap3593swap_checked : acceptsGraphIso
    (fused (graph core3593) (root 8) 6 0) DegreeTwoThreeSpectrum5731.graph fusedMap3593swap=true := by decide +kernel
theorem certified3593swap : Certified (graph core3593) (root 8) 6 0 :=
  of_native_maps core3593 DegreeTwoThreeSpectrum5729.graph DegreeTwoThreeSpectrum5731.graph
    sourceMap3593swap fusedMap3593swap sourceMap3593swap_checked fusedMap3593swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3593
#print axioms sourceMap3593swap_checked
#print axioms fusedMap3593swap_checked
#print axioms certified3593swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
