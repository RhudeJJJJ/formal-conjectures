/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3315 : Family 9 := level9.get ⟨280,by decide⟩
def sourceMap3315 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3315 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3315_checked : acceptsGraphIso
    (source (graph core3315) (root 9) 0 5) DegreeTwoThreeSpectrum5779.graph sourceMap3315=true := by decide +kernel
theorem fusedMap3315_checked : acceptsGraphIso
    (fused (graph core3315) (root 9) 0 5) DegreeTwoThreeSpectrum5780.graph fusedMap3315=true := by decide +kernel
theorem certified3315 : Certified (graph core3315) (root 9) 0 5 :=
  of_native_maps core3315 DegreeTwoThreeSpectrum5779.graph DegreeTwoThreeSpectrum5780.graph
    sourceMap3315 fusedMap3315 sourceMap3315_checked fusedMap3315_checked
    DegreeTwoThreeFiniteComparisons.comparison3315
#print axioms sourceMap3315_checked
#print axioms fusedMap3315_checked
#print axioms certified3315
def sourceMap3315swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3315swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3315swap_checked : acceptsGraphIso
    (source (graph core3315) (root 9) 5 0) DegreeTwoThreeSpectrum5779.graph sourceMap3315swap=true := by decide +kernel
theorem fusedMap3315swap_checked : acceptsGraphIso
    (fused (graph core3315) (root 9) 5 0) DegreeTwoThreeSpectrum5780.graph fusedMap3315swap=true := by decide +kernel
theorem certified3315swap : Certified (graph core3315) (root 9) 5 0 :=
  of_native_maps core3315 DegreeTwoThreeSpectrum5779.graph DegreeTwoThreeSpectrum5780.graph
    sourceMap3315swap fusedMap3315swap sourceMap3315swap_checked fusedMap3315swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3315
#print axioms sourceMap3315swap_checked
#print axioms fusedMap3315swap_checked
#print axioms certified3315swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
