/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3545 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap3545 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3545 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3545_checked : acceptsGraphIso
    (source (graph core3545) (root 8) 0 6) DegreeTwoThreeSpectrum5126.graph sourceMap3545=true := by decide +kernel
theorem fusedMap3545_checked : acceptsGraphIso
    (fused (graph core3545) (root 8) 0 6) DegreeTwoThreeSpectrum5128.graph fusedMap3545=true := by decide +kernel
theorem certified3545 : Certified (graph core3545) (root 8) 0 6 :=
  of_native_maps core3545 DegreeTwoThreeSpectrum5126.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap3545 fusedMap3545 sourceMap3545_checked fusedMap3545_checked
    DegreeTwoThreeFiniteComparisons.comparison3545
#print axioms sourceMap3545_checked
#print axioms fusedMap3545_checked
#print axioms certified3545
def sourceMap3545swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,9] (sourceLabel 8 6 0 v)
def fusedMap3545swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3545swap_checked : acceptsGraphIso
    (source (graph core3545) (root 8) 6 0) DegreeTwoThreeSpectrum5126.graph sourceMap3545swap=true := by decide +kernel
theorem fusedMap3545swap_checked : acceptsGraphIso
    (fused (graph core3545) (root 8) 6 0) DegreeTwoThreeSpectrum5128.graph fusedMap3545swap=true := by decide +kernel
theorem certified3545swap : Certified (graph core3545) (root 8) 6 0 :=
  of_native_maps core3545 DegreeTwoThreeSpectrum5126.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap3545swap fusedMap3545swap sourceMap3545swap_checked fusedMap3545swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3545
#print axioms sourceMap3545swap_checked
#print axioms fusedMap3545swap_checked
#print axioms certified3545swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
