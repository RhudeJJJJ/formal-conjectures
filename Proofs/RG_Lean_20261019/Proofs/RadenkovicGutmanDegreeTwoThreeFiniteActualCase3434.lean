/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3434 : Family 9 := level9.get ⟨574,by decide⟩
def sourceMap3434 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3434 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3434_checked : acceptsGraphIso
    (source (graph core3434) (root 9) 0 5) DegreeTwoThreeSpectrum6095.graph sourceMap3434=true := by decide +kernel
theorem fusedMap3434_checked : acceptsGraphIso
    (fused (graph core3434) (root 9) 0 5) DegreeTwoThreeSpectrum6096.graph fusedMap3434=true := by decide +kernel
theorem certified3434 : Certified (graph core3434) (root 9) 0 5 :=
  of_native_maps core3434 DegreeTwoThreeSpectrum6095.graph DegreeTwoThreeSpectrum6096.graph
    sourceMap3434 fusedMap3434 sourceMap3434_checked fusedMap3434_checked
    DegreeTwoThreeFiniteComparisons.comparison3434
#print axioms sourceMap3434_checked
#print axioms fusedMap3434_checked
#print axioms certified3434
def sourceMap3434swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3434swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3434swap_checked : acceptsGraphIso
    (source (graph core3434) (root 9) 5 0) DegreeTwoThreeSpectrum6095.graph sourceMap3434swap=true := by decide +kernel
theorem fusedMap3434swap_checked : acceptsGraphIso
    (fused (graph core3434) (root 9) 5 0) DegreeTwoThreeSpectrum6096.graph fusedMap3434swap=true := by decide +kernel
theorem certified3434swap : Certified (graph core3434) (root 9) 5 0 :=
  of_native_maps core3434 DegreeTwoThreeSpectrum6095.graph DegreeTwoThreeSpectrum6096.graph
    sourceMap3434swap fusedMap3434swap sourceMap3434swap_checked fusedMap3434swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3434
#print axioms sourceMap3434swap_checked
#print axioms fusedMap3434swap_checked
#print axioms certified3434swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
