/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3405 : Family 9 := level9.get ⟨505,by decide⟩
def sourceMap3405 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3405 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3405_checked : acceptsGraphIso
    (source (graph core3405) (root 9) 0 5) DegreeTwoThreeSpectrum6922.graph sourceMap3405=true := by decide +kernel
theorem fusedMap3405_checked : acceptsGraphIso
    (fused (graph core3405) (root 9) 0 5) DegreeTwoThreeSpectrum5703.graph fusedMap3405=true := by decide +kernel
theorem certified3405 : Certified (graph core3405) (root 9) 0 5 :=
  of_native_maps core3405 DegreeTwoThreeSpectrum6922.graph DegreeTwoThreeSpectrum5703.graph
    sourceMap3405 fusedMap3405 sourceMap3405_checked fusedMap3405_checked
    DegreeTwoThreeFiniteComparisons.comparison3405
#print axioms sourceMap3405_checked
#print axioms fusedMap3405_checked
#print axioms certified3405
def sourceMap3405swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3405swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3405swap_checked : acceptsGraphIso
    (source (graph core3405) (root 9) 5 0) DegreeTwoThreeSpectrum6922.graph sourceMap3405swap=true := by decide +kernel
theorem fusedMap3405swap_checked : acceptsGraphIso
    (fused (graph core3405) (root 9) 5 0) DegreeTwoThreeSpectrum5703.graph fusedMap3405swap=true := by decide +kernel
theorem certified3405swap : Certified (graph core3405) (root 9) 5 0 :=
  of_native_maps core3405 DegreeTwoThreeSpectrum6922.graph DegreeTwoThreeSpectrum5703.graph
    sourceMap3405swap fusedMap3405swap sourceMap3405swap_checked fusedMap3405swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3405
#print axioms sourceMap3405swap_checked
#print axioms fusedMap3405swap_checked
#print axioms certified3405swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
