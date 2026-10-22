/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3560 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap3560 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3560 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3560_checked : acceptsGraphIso
    (source (graph core3560) (root 8) 0 6) DegreeTwoThreeSpectrum5861.graph sourceMap3560=true := by decide +kernel
theorem fusedMap3560_checked : acceptsGraphIso
    (fused (graph core3560) (root 8) 0 6) DegreeTwoThreeSpectrum5084.graph fusedMap3560=true := by decide +kernel
theorem certified3560 : Certified (graph core3560) (root 8) 0 6 :=
  of_native_maps core3560 DegreeTwoThreeSpectrum5861.graph DegreeTwoThreeSpectrum5084.graph
    sourceMap3560 fusedMap3560 sourceMap3560_checked fusedMap3560_checked
    DegreeTwoThreeFiniteComparisons.comparison3560
#print axioms sourceMap3560_checked
#print axioms fusedMap3560_checked
#print axioms certified3560
def sourceMap3560swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3560swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3560swap_checked : acceptsGraphIso
    (source (graph core3560) (root 8) 6 0) DegreeTwoThreeSpectrum5861.graph sourceMap3560swap=true := by decide +kernel
theorem fusedMap3560swap_checked : acceptsGraphIso
    (fused (graph core3560) (root 8) 6 0) DegreeTwoThreeSpectrum5084.graph fusedMap3560swap=true := by decide +kernel
theorem certified3560swap : Certified (graph core3560) (root 8) 6 0 :=
  of_native_maps core3560 DegreeTwoThreeSpectrum5861.graph DegreeTwoThreeSpectrum5084.graph
    sourceMap3560swap fusedMap3560swap sourceMap3560swap_checked fusedMap3560swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3560
#print axioms sourceMap3560swap_checked
#print axioms fusedMap3560swap_checked
#print axioms certified3560swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
