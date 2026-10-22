/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3384 : Family 9 := level9.get ⟨455,by decide⟩
def sourceMap3384 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3384 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3384_checked : acceptsGraphIso
    (source (graph core3384) (root 9) 0 5) DegreeTwoThreeSpectrum6663.graph sourceMap3384=true := by decide +kernel
theorem fusedMap3384_checked : acceptsGraphIso
    (fused (graph core3384) (root 9) 0 5) DegreeTwoThreeSpectrum5518.graph fusedMap3384=true := by decide +kernel
theorem certified3384 : Certified (graph core3384) (root 9) 0 5 :=
  of_native_maps core3384 DegreeTwoThreeSpectrum6663.graph DegreeTwoThreeSpectrum5518.graph
    sourceMap3384 fusedMap3384 sourceMap3384_checked fusedMap3384_checked
    DegreeTwoThreeFiniteComparisons.comparison3384
#print axioms sourceMap3384_checked
#print axioms fusedMap3384_checked
#print axioms certified3384
def sourceMap3384swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3384swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3384swap_checked : acceptsGraphIso
    (source (graph core3384) (root 9) 5 0) DegreeTwoThreeSpectrum6663.graph sourceMap3384swap=true := by decide +kernel
theorem fusedMap3384swap_checked : acceptsGraphIso
    (fused (graph core3384) (root 9) 5 0) DegreeTwoThreeSpectrum5518.graph fusedMap3384swap=true := by decide +kernel
theorem certified3384swap : Certified (graph core3384) (root 9) 5 0 :=
  of_native_maps core3384 DegreeTwoThreeSpectrum6663.graph DegreeTwoThreeSpectrum5518.graph
    sourceMap3384swap fusedMap3384swap sourceMap3384swap_checked fusedMap3384swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3384
#print axioms sourceMap3384swap_checked
#print axioms fusedMap3384swap_checked
#print axioms certified3384swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
