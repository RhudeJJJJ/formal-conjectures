/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3188 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap3188 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3188 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3188_checked : acceptsGraphIso
    (source (graph core3188) (root 8) 0 5) DegreeTwoThreeSpectrum4523.graph sourceMap3188=true := by decide +kernel
theorem fusedMap3188_checked : acceptsGraphIso
    (fused (graph core3188) (root 8) 0 5) DegreeTwoThreeSpectrum4036.graph fusedMap3188=true := by decide +kernel
theorem certified3188 : Certified (graph core3188) (root 8) 0 5 :=
  of_native_maps core3188 DegreeTwoThreeSpectrum4523.graph DegreeTwoThreeSpectrum4036.graph
    sourceMap3188 fusedMap3188 sourceMap3188_checked fusedMap3188_checked
    DegreeTwoThreeFiniteComparisons.comparison3188
#print axioms sourceMap3188_checked
#print axioms fusedMap3188_checked
#print axioms certified3188
def sourceMap3188swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3188swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3188swap_checked : acceptsGraphIso
    (source (graph core3188) (root 8) 5 0) DegreeTwoThreeSpectrum4523.graph sourceMap3188swap=true := by decide +kernel
theorem fusedMap3188swap_checked : acceptsGraphIso
    (fused (graph core3188) (root 8) 5 0) DegreeTwoThreeSpectrum4036.graph fusedMap3188swap=true := by decide +kernel
theorem certified3188swap : Certified (graph core3188) (root 8) 5 0 :=
  of_native_maps core3188 DegreeTwoThreeSpectrum4523.graph DegreeTwoThreeSpectrum4036.graph
    sourceMap3188swap fusedMap3188swap sourceMap3188swap_checked fusedMap3188swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3188
#print axioms sourceMap3188swap_checked
#print axioms fusedMap3188swap_checked
#print axioms certified3188swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
