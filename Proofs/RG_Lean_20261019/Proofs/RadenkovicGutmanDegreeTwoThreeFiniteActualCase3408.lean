/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3408 : Family 9 := level9.get ⟨511,by decide⟩
def sourceMap3408 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3408 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3408_checked : acceptsGraphIso
    (source (graph core3408) (root 9) 0 5) DegreeTwoThreeSpectrum6941.graph sourceMap3408=true := by decide +kernel
theorem fusedMap3408_checked : acceptsGraphIso
    (fused (graph core3408) (root 9) 0 5) DegreeTwoThreeSpectrum5728.graph fusedMap3408=true := by decide +kernel
theorem certified3408 : Certified (graph core3408) (root 9) 0 5 :=
  of_native_maps core3408 DegreeTwoThreeSpectrum6941.graph DegreeTwoThreeSpectrum5728.graph
    sourceMap3408 fusedMap3408 sourceMap3408_checked fusedMap3408_checked
    DegreeTwoThreeFiniteComparisons.comparison3408
#print axioms sourceMap3408_checked
#print axioms fusedMap3408_checked
#print axioms certified3408
def sourceMap3408swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3408swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3408swap_checked : acceptsGraphIso
    (source (graph core3408) (root 9) 5 0) DegreeTwoThreeSpectrum6941.graph sourceMap3408swap=true := by decide +kernel
theorem fusedMap3408swap_checked : acceptsGraphIso
    (fused (graph core3408) (root 9) 5 0) DegreeTwoThreeSpectrum5728.graph fusedMap3408swap=true := by decide +kernel
theorem certified3408swap : Certified (graph core3408) (root 9) 5 0 :=
  of_native_maps core3408 DegreeTwoThreeSpectrum6941.graph DegreeTwoThreeSpectrum5728.graph
    sourceMap3408swap fusedMap3408swap sourceMap3408swap_checked fusedMap3408swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3408
#print axioms sourceMap3408swap_checked
#print axioms fusedMap3408swap_checked
#print axioms certified3408swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
