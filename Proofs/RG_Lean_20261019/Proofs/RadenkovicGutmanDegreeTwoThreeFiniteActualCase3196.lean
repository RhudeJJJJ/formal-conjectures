/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3196 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap3196 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3196 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3196_checked : acceptsGraphIso
    (source (graph core3196) (root 8) 0 5) DegreeTwoThreeSpectrum4614.graph sourceMap3196=true := by decide +kernel
theorem fusedMap3196_checked : acceptsGraphIso
    (fused (graph core3196) (root 8) 0 5) DegreeTwoThreeSpectrum4092.graph fusedMap3196=true := by decide +kernel
theorem certified3196 : Certified (graph core3196) (root 8) 0 5 :=
  of_native_maps core3196 DegreeTwoThreeSpectrum4614.graph DegreeTwoThreeSpectrum4092.graph
    sourceMap3196 fusedMap3196 sourceMap3196_checked fusedMap3196_checked
    DegreeTwoThreeFiniteComparisons.comparison3196
#print axioms sourceMap3196_checked
#print axioms fusedMap3196_checked
#print axioms certified3196
def sourceMap3196swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3196swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3196swap_checked : acceptsGraphIso
    (source (graph core3196) (root 8) 5 0) DegreeTwoThreeSpectrum4614.graph sourceMap3196swap=true := by decide +kernel
theorem fusedMap3196swap_checked : acceptsGraphIso
    (fused (graph core3196) (root 8) 5 0) DegreeTwoThreeSpectrum4092.graph fusedMap3196swap=true := by decide +kernel
theorem certified3196swap : Certified (graph core3196) (root 8) 5 0 :=
  of_native_maps core3196 DegreeTwoThreeSpectrum4614.graph DegreeTwoThreeSpectrum4092.graph
    sourceMap3196swap fusedMap3196swap sourceMap3196swap_checked fusedMap3196swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3196
#print axioms sourceMap3196swap_checked
#print axioms fusedMap3196swap_checked
#print axioms certified3196swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
