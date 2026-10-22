/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3546 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap3546 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3546 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3546_checked : acceptsGraphIso
    (source (graph core3546) (root 8) 0 6) DegreeTwoThreeSpectrum5217.graph sourceMap3546=true := by decide +kernel
theorem fusedMap3546_checked : acceptsGraphIso
    (fused (graph core3546) (root 8) 0 6) DegreeTwoThreeSpectrum4969.graph fusedMap3546=true := by decide +kernel
theorem certified3546 : Certified (graph core3546) (root 8) 0 6 :=
  of_native_maps core3546 DegreeTwoThreeSpectrum5217.graph DegreeTwoThreeSpectrum4969.graph
    sourceMap3546 fusedMap3546 sourceMap3546_checked fusedMap3546_checked
    DegreeTwoThreeFiniteComparisons.comparison3546
#print axioms sourceMap3546_checked
#print axioms fusedMap3546_checked
#print axioms certified3546
def sourceMap3546swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3546swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3546swap_checked : acceptsGraphIso
    (source (graph core3546) (root 8) 6 0) DegreeTwoThreeSpectrum5217.graph sourceMap3546swap=true := by decide +kernel
theorem fusedMap3546swap_checked : acceptsGraphIso
    (fused (graph core3546) (root 8) 6 0) DegreeTwoThreeSpectrum4969.graph fusedMap3546swap=true := by decide +kernel
theorem certified3546swap : Certified (graph core3546) (root 8) 6 0 :=
  of_native_maps core3546 DegreeTwoThreeSpectrum5217.graph DegreeTwoThreeSpectrum4969.graph
    sourceMap3546swap fusedMap3546swap sourceMap3546swap_checked fusedMap3546swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3546
#print axioms sourceMap3546swap_checked
#print axioms fusedMap3546swap_checked
#print axioms certified3546swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
