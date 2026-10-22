/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3428 : Family 9 := level9.get ⟨563,by decide⟩
def sourceMap3428 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3428 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3428_checked : acceptsGraphIso
    (source (graph core3428) (root 9) 0 5) DegreeTwoThreeSpectrum6051.graph sourceMap3428=true := by decide +kernel
theorem fusedMap3428_checked : acceptsGraphIso
    (fused (graph core3428) (root 9) 0 5) DegreeTwoThreeSpectrum6052.graph fusedMap3428=true := by decide +kernel
theorem certified3428 : Certified (graph core3428) (root 9) 0 5 :=
  of_native_maps core3428 DegreeTwoThreeSpectrum6051.graph DegreeTwoThreeSpectrum6052.graph
    sourceMap3428 fusedMap3428 sourceMap3428_checked fusedMap3428_checked
    DegreeTwoThreeFiniteComparisons.comparison3428
#print axioms sourceMap3428_checked
#print axioms fusedMap3428_checked
#print axioms certified3428
def sourceMap3428swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3428swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3428swap_checked : acceptsGraphIso
    (source (graph core3428) (root 9) 5 0) DegreeTwoThreeSpectrum6051.graph sourceMap3428swap=true := by decide +kernel
theorem fusedMap3428swap_checked : acceptsGraphIso
    (fused (graph core3428) (root 9) 5 0) DegreeTwoThreeSpectrum6052.graph fusedMap3428swap=true := by decide +kernel
theorem certified3428swap : Certified (graph core3428) (root 9) 5 0 :=
  of_native_maps core3428 DegreeTwoThreeSpectrum6051.graph DegreeTwoThreeSpectrum6052.graph
    sourceMap3428swap fusedMap3428swap sourceMap3428swap_checked fusedMap3428swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3428
#print axioms sourceMap3428swap_checked
#print axioms fusedMap3428swap_checked
#print axioms certified3428swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
