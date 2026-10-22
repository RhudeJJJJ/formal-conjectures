/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3292 : Family 9 := level9.get ⟨211,by decide⟩
def sourceMap3292 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3292 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3292_checked : acceptsGraphIso
    (source (graph core3292) (root 9) 0 5) DegreeTwoThreeSpectrum5473.graph sourceMap3292=true := by decide +kernel
theorem fusedMap3292_checked : acceptsGraphIso
    (fused (graph core3292) (root 9) 0 5) DegreeTwoThreeSpectrum5474.graph fusedMap3292=true := by decide +kernel
theorem certified3292 : Certified (graph core3292) (root 9) 0 5 :=
  of_native_maps core3292 DegreeTwoThreeSpectrum5473.graph DegreeTwoThreeSpectrum5474.graph
    sourceMap3292 fusedMap3292 sourceMap3292_checked fusedMap3292_checked
    DegreeTwoThreeFiniteComparisons.comparison3292
#print axioms sourceMap3292_checked
#print axioms fusedMap3292_checked
#print axioms certified3292
def sourceMap3292swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3292swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3292swap_checked : acceptsGraphIso
    (source (graph core3292) (root 9) 5 0) DegreeTwoThreeSpectrum5473.graph sourceMap3292swap=true := by decide +kernel
theorem fusedMap3292swap_checked : acceptsGraphIso
    (fused (graph core3292) (root 9) 5 0) DegreeTwoThreeSpectrum5474.graph fusedMap3292swap=true := by decide +kernel
theorem certified3292swap : Certified (graph core3292) (root 9) 5 0 :=
  of_native_maps core3292 DegreeTwoThreeSpectrum5473.graph DegreeTwoThreeSpectrum5474.graph
    sourceMap3292swap fusedMap3292swap sourceMap3292swap_checked fusedMap3292swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3292
#print axioms sourceMap3292swap_checked
#print axioms fusedMap3292swap_checked
#print axioms certified3292swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
