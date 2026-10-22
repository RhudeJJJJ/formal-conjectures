/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3281 : Family 9 := level9.get ⟨181,by decide⟩
def sourceMap3281 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3281 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3281_checked : acceptsGraphIso
    (source (graph core3281) (root 9) 0 5) DegreeTwoThreeSpectrum5335.graph sourceMap3281=true := by decide +kernel
theorem fusedMap3281_checked : acceptsGraphIso
    (fused (graph core3281) (root 9) 0 5) DegreeTwoThreeSpectrum5336.graph fusedMap3281=true := by decide +kernel
theorem certified3281 : Certified (graph core3281) (root 9) 0 5 :=
  of_native_maps core3281 DegreeTwoThreeSpectrum5335.graph DegreeTwoThreeSpectrum5336.graph
    sourceMap3281 fusedMap3281 sourceMap3281_checked fusedMap3281_checked
    DegreeTwoThreeFiniteComparisons.comparison3281
#print axioms sourceMap3281_checked
#print axioms fusedMap3281_checked
#print axioms certified3281
def sourceMap3281swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3281swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3281swap_checked : acceptsGraphIso
    (source (graph core3281) (root 9) 5 0) DegreeTwoThreeSpectrum5335.graph sourceMap3281swap=true := by decide +kernel
theorem fusedMap3281swap_checked : acceptsGraphIso
    (fused (graph core3281) (root 9) 5 0) DegreeTwoThreeSpectrum5336.graph fusedMap3281swap=true := by decide +kernel
theorem certified3281swap : Certified (graph core3281) (root 9) 5 0 :=
  of_native_maps core3281 DegreeTwoThreeSpectrum5335.graph DegreeTwoThreeSpectrum5336.graph
    sourceMap3281swap fusedMap3281swap sourceMap3281swap_checked fusedMap3281swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3281
#print axioms sourceMap3281swap_checked
#print axioms fusedMap3281swap_checked
#print axioms certified3281swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
