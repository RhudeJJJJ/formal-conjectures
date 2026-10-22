/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3245 : Family 9 := level9.get ⟨54,by decide⟩
def sourceMap3245 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3245 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3245_checked : acceptsGraphIso
    (source (graph core3245) (root 9) 0 5) DegreeTwoThreeSpectrum5304.graph sourceMap3245=true := by decide +kernel
theorem fusedMap3245_checked : acceptsGraphIso
    (fused (graph core3245) (root 9) 0 5) DegreeTwoThreeSpectrum4978.graph fusedMap3245=true := by decide +kernel
theorem certified3245 : Certified (graph core3245) (root 9) 0 5 :=
  of_native_maps core3245 DegreeTwoThreeSpectrum5304.graph DegreeTwoThreeSpectrum4978.graph
    sourceMap3245 fusedMap3245 sourceMap3245_checked fusedMap3245_checked
    DegreeTwoThreeFiniteComparisons.comparison3245
#print axioms sourceMap3245_checked
#print axioms fusedMap3245_checked
#print axioms certified3245
def sourceMap3245swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3245swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3245swap_checked : acceptsGraphIso
    (source (graph core3245) (root 9) 5 0) DegreeTwoThreeSpectrum5304.graph sourceMap3245swap=true := by decide +kernel
theorem fusedMap3245swap_checked : acceptsGraphIso
    (fused (graph core3245) (root 9) 5 0) DegreeTwoThreeSpectrum4978.graph fusedMap3245swap=true := by decide +kernel
theorem certified3245swap : Certified (graph core3245) (root 9) 5 0 :=
  of_native_maps core3245 DegreeTwoThreeSpectrum5304.graph DegreeTwoThreeSpectrum4978.graph
    sourceMap3245swap fusedMap3245swap sourceMap3245swap_checked fusedMap3245swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3245
#print axioms sourceMap3245swap_checked
#print axioms fusedMap3245swap_checked
#print axioms certified3245swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
