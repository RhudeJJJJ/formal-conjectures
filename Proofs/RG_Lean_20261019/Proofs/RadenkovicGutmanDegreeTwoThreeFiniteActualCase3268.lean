/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3268 : Family 9 := level9.get ⟨133,by decide⟩
def sourceMap3268 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 9 0 5 v)
def fusedMap3268 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3268_checked : acceptsGraphIso
    (source (graph core3268) (root 9) 0 5) DegreeTwoThreeSpectrum5956.graph sourceMap3268=true := by decide +kernel
theorem fusedMap3268_checked : acceptsGraphIso
    (fused (graph core3268) (root 9) 0 5) DegreeTwoThreeSpectrum5124.graph fusedMap3268=true := by decide +kernel
theorem certified3268 : Certified (graph core3268) (root 9) 0 5 :=
  of_native_maps core3268 DegreeTwoThreeSpectrum5956.graph DegreeTwoThreeSpectrum5124.graph
    sourceMap3268 fusedMap3268 sourceMap3268_checked fusedMap3268_checked
    DegreeTwoThreeFiniteComparisons.comparison3268
#print axioms sourceMap3268_checked
#print axioms fusedMap3268_checked
#print axioms certified3268
def sourceMap3268swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12,16] (sourceLabel 9 5 0 v)
def fusedMap3268swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3268swap_checked : acceptsGraphIso
    (source (graph core3268) (root 9) 5 0) DegreeTwoThreeSpectrum5956.graph sourceMap3268swap=true := by decide +kernel
theorem fusedMap3268swap_checked : acceptsGraphIso
    (fused (graph core3268) (root 9) 5 0) DegreeTwoThreeSpectrum5124.graph fusedMap3268swap=true := by decide +kernel
theorem certified3268swap : Certified (graph core3268) (root 9) 5 0 :=
  of_native_maps core3268 DegreeTwoThreeSpectrum5956.graph DegreeTwoThreeSpectrum5124.graph
    sourceMap3268swap fusedMap3268swap sourceMap3268swap_checked fusedMap3268swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3268
#print axioms sourceMap3268swap_checked
#print axioms fusedMap3268swap_checked
#print axioms certified3268swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
