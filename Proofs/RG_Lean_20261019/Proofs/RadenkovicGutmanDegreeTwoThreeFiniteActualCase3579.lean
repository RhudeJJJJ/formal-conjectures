/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3579 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap3579 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3579 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3579_checked : acceptsGraphIso
    (source (graph core3579) (root 8) 0 6) DegreeTwoThreeSpectrum5451.graph sourceMap3579=true := by decide +kernel
theorem fusedMap3579_checked : acceptsGraphIso
    (fused (graph core3579) (root 8) 0 6) DegreeTwoThreeSpectrum5453.graph fusedMap3579=true := by decide +kernel
theorem certified3579 : Certified (graph core3579) (root 8) 0 6 :=
  of_native_maps core3579 DegreeTwoThreeSpectrum5451.graph DegreeTwoThreeSpectrum5453.graph
    sourceMap3579 fusedMap3579 sourceMap3579_checked fusedMap3579_checked
    DegreeTwoThreeFiniteComparisons.comparison3579
#print axioms sourceMap3579_checked
#print axioms fusedMap3579_checked
#print axioms certified3579
def sourceMap3579swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3579swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3579swap_checked : acceptsGraphIso
    (source (graph core3579) (root 8) 6 0) DegreeTwoThreeSpectrum5451.graph sourceMap3579swap=true := by decide +kernel
theorem fusedMap3579swap_checked : acceptsGraphIso
    (fused (graph core3579) (root 8) 6 0) DegreeTwoThreeSpectrum5453.graph fusedMap3579swap=true := by decide +kernel
theorem certified3579swap : Certified (graph core3579) (root 8) 6 0 :=
  of_native_maps core3579 DegreeTwoThreeSpectrum5451.graph DegreeTwoThreeSpectrum5453.graph
    sourceMap3579swap fusedMap3579swap sourceMap3579swap_checked fusedMap3579swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3579
#print axioms sourceMap3579swap_checked
#print axioms fusedMap3579swap_checked
#print axioms certified3579swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
