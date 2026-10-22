/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3276 : Family 9 := level9.get ⟨164,by decide⟩
def sourceMap3276 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3276 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3276_checked : acceptsGraphIso
    (source (graph core3276) (root 9) 0 5) DegreeTwoThreeSpectrum5260.graph sourceMap3276=true := by decide +kernel
theorem fusedMap3276_checked : acceptsGraphIso
    (fused (graph core3276) (root 9) 0 5) DegreeTwoThreeSpectrum5261.graph fusedMap3276=true := by decide +kernel
theorem certified3276 : Certified (graph core3276) (root 9) 0 5 :=
  of_native_maps core3276 DegreeTwoThreeSpectrum5260.graph DegreeTwoThreeSpectrum5261.graph
    sourceMap3276 fusedMap3276 sourceMap3276_checked fusedMap3276_checked
    DegreeTwoThreeFiniteComparisons.comparison3276
#print axioms sourceMap3276_checked
#print axioms fusedMap3276_checked
#print axioms certified3276
def sourceMap3276swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3276swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3276swap_checked : acceptsGraphIso
    (source (graph core3276) (root 9) 5 0) DegreeTwoThreeSpectrum5260.graph sourceMap3276swap=true := by decide +kernel
theorem fusedMap3276swap_checked : acceptsGraphIso
    (fused (graph core3276) (root 9) 5 0) DegreeTwoThreeSpectrum5261.graph fusedMap3276swap=true := by decide +kernel
theorem certified3276swap : Certified (graph core3276) (root 9) 5 0 :=
  of_native_maps core3276 DegreeTwoThreeSpectrum5260.graph DegreeTwoThreeSpectrum5261.graph
    sourceMap3276swap fusedMap3276swap sourceMap3276swap_checked fusedMap3276swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3276
#print axioms sourceMap3276swap_checked
#print axioms fusedMap3276swap_checked
#print axioms certified3276swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
