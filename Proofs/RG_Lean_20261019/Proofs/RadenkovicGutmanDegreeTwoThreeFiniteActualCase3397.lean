/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3397 : Family 9 := level9.get ⟨488,by decide⟩
def sourceMap3397 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3397 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3397_checked : acceptsGraphIso
    (source (graph core3397) (root 9) 0 5) DegreeTwoThreeSpectrum6828.graph sourceMap3397=true := by decide +kernel
theorem fusedMap3397_checked : acceptsGraphIso
    (fused (graph core3397) (root 9) 0 5) DegreeTwoThreeSpectrum5656.graph fusedMap3397=true := by decide +kernel
theorem certified3397 : Certified (graph core3397) (root 9) 0 5 :=
  of_native_maps core3397 DegreeTwoThreeSpectrum6828.graph DegreeTwoThreeSpectrum5656.graph
    sourceMap3397 fusedMap3397 sourceMap3397_checked fusedMap3397_checked
    DegreeTwoThreeFiniteComparisons.comparison3397
#print axioms sourceMap3397_checked
#print axioms fusedMap3397_checked
#print axioms certified3397
def sourceMap3397swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3397swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3397swap_checked : acceptsGraphIso
    (source (graph core3397) (root 9) 5 0) DegreeTwoThreeSpectrum6828.graph sourceMap3397swap=true := by decide +kernel
theorem fusedMap3397swap_checked : acceptsGraphIso
    (fused (graph core3397) (root 9) 5 0) DegreeTwoThreeSpectrum5656.graph fusedMap3397swap=true := by decide +kernel
theorem certified3397swap : Certified (graph core3397) (root 9) 5 0 :=
  of_native_maps core3397 DegreeTwoThreeSpectrum6828.graph DegreeTwoThreeSpectrum5656.graph
    sourceMap3397swap fusedMap3397swap sourceMap3397swap_checked fusedMap3397swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3397
#print axioms sourceMap3397swap_checked
#print axioms fusedMap3397swap_checked
#print axioms certified3397swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
