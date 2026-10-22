/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3385 : Family 9 := level9.get ⟨460,by decide⟩
def sourceMap3385 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3385 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3385_checked : acceptsGraphIso
    (source (graph core3385) (root 9) 0 5) DegreeTwoThreeSpectrum6683.graph sourceMap3385=true := by decide +kernel
theorem fusedMap3385_checked : acceptsGraphIso
    (fused (graph core3385) (root 9) 0 5) DegreeTwoThreeSpectrum5542.graph fusedMap3385=true := by decide +kernel
theorem certified3385 : Certified (graph core3385) (root 9) 0 5 :=
  of_native_maps core3385 DegreeTwoThreeSpectrum6683.graph DegreeTwoThreeSpectrum5542.graph
    sourceMap3385 fusedMap3385 sourceMap3385_checked fusedMap3385_checked
    DegreeTwoThreeFiniteComparisons.comparison3385
#print axioms sourceMap3385_checked
#print axioms fusedMap3385_checked
#print axioms certified3385
def sourceMap3385swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3385swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3385swap_checked : acceptsGraphIso
    (source (graph core3385) (root 9) 5 0) DegreeTwoThreeSpectrum6683.graph sourceMap3385swap=true := by decide +kernel
theorem fusedMap3385swap_checked : acceptsGraphIso
    (fused (graph core3385) (root 9) 5 0) DegreeTwoThreeSpectrum5542.graph fusedMap3385swap=true := by decide +kernel
theorem certified3385swap : Certified (graph core3385) (root 9) 5 0 :=
  of_native_maps core3385 DegreeTwoThreeSpectrum6683.graph DegreeTwoThreeSpectrum5542.graph
    sourceMap3385swap fusedMap3385swap sourceMap3385swap_checked fusedMap3385swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3385
#print axioms sourceMap3385swap_checked
#print axioms fusedMap3385swap_checked
#print axioms certified3385swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
