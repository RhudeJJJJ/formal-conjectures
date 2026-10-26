/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3683 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap3683 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3683 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3683_checked : acceptsGraphIso
    (source (graph core3683) (root 7) 0 7) DegreeTwoThreeSpectrum5185.graph sourceMap3683=true := by decide +kernel
theorem fusedMap3683_checked : acceptsGraphIso
    (fused (graph core3683) (root 7) 0 7) DegreeTwoThreeSpectrum5188.graph fusedMap3683=true := by decide +kernel
theorem certified3683 : Certified (graph core3683) (root 7) 0 7 :=
  of_native_maps core3683 DegreeTwoThreeSpectrum5185.graph DegreeTwoThreeSpectrum5188.graph
    sourceMap3683 fusedMap3683 sourceMap3683_checked fusedMap3683_checked
    DegreeTwoThreeFiniteComparisons.comparison3683
#print axioms sourceMap3683_checked
#print axioms fusedMap3683_checked
#print axioms certified3683
def sourceMap3683swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3683swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3683swap_checked : acceptsGraphIso
    (source (graph core3683) (root 7) 7 0) DegreeTwoThreeSpectrum5185.graph sourceMap3683swap=true := by decide +kernel
theorem fusedMap3683swap_checked : acceptsGraphIso
    (fused (graph core3683) (root 7) 7 0) DegreeTwoThreeSpectrum5188.graph fusedMap3683swap=true := by decide +kernel
theorem certified3683swap : Certified (graph core3683) (root 7) 7 0 :=
  of_native_maps core3683 DegreeTwoThreeSpectrum5185.graph DegreeTwoThreeSpectrum5188.graph
    sourceMap3683swap fusedMap3683swap sourceMap3683swap_checked fusedMap3683swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3683
#print axioms sourceMap3683swap_checked
#print axioms fusedMap3683swap_checked
#print axioms certified3683swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
