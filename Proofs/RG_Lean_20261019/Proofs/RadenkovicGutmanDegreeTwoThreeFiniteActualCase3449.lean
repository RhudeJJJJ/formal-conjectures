/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3449 : Family 9 := level9.get ⟨608,by decide⟩
def sourceMap3449 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3449 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3449_checked : acceptsGraphIso
    (source (graph core3449) (root 9) 0 5) DegreeTwoThreeSpectrum6279.graph sourceMap3449=true := by decide +kernel
theorem fusedMap3449_checked : acceptsGraphIso
    (fused (graph core3449) (root 9) 0 5) DegreeTwoThreeSpectrum6280.graph fusedMap3449=true := by decide +kernel
theorem certified3449 : Certified (graph core3449) (root 9) 0 5 :=
  of_native_maps core3449 DegreeTwoThreeSpectrum6279.graph DegreeTwoThreeSpectrum6280.graph
    sourceMap3449 fusedMap3449 sourceMap3449_checked fusedMap3449_checked
    DegreeTwoThreeFiniteComparisons.comparison3449
#print axioms sourceMap3449_checked
#print axioms fusedMap3449_checked
#print axioms certified3449
def sourceMap3449swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3449swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3449swap_checked : acceptsGraphIso
    (source (graph core3449) (root 9) 5 0) DegreeTwoThreeSpectrum6279.graph sourceMap3449swap=true := by decide +kernel
theorem fusedMap3449swap_checked : acceptsGraphIso
    (fused (graph core3449) (root 9) 5 0) DegreeTwoThreeSpectrum6280.graph fusedMap3449swap=true := by decide +kernel
theorem certified3449swap : Certified (graph core3449) (root 9) 5 0 :=
  of_native_maps core3449 DegreeTwoThreeSpectrum6279.graph DegreeTwoThreeSpectrum6280.graph
    sourceMap3449swap fusedMap3449swap sourceMap3449swap_checked fusedMap3449swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3449
#print axioms sourceMap3449swap_checked
#print axioms fusedMap3449swap_checked
#print axioms certified3449swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
