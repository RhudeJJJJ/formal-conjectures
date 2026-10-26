/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3583 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap3583 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3583 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3583_checked : acceptsGraphIso
    (source (graph core3583) (root 8) 0 6) DegreeTwoThreeSpectrum5519.graph sourceMap3583=true := by decide +kernel
theorem fusedMap3583_checked : acceptsGraphIso
    (fused (graph core3583) (root 8) 0 6) DegreeTwoThreeSpectrum5521.graph fusedMap3583=true := by decide +kernel
theorem certified3583 : Certified (graph core3583) (root 8) 0 6 :=
  of_native_maps core3583 DegreeTwoThreeSpectrum5519.graph DegreeTwoThreeSpectrum5521.graph
    sourceMap3583 fusedMap3583 sourceMap3583_checked fusedMap3583_checked
    DegreeTwoThreeFiniteComparisons.comparison3583
#print axioms sourceMap3583_checked
#print axioms fusedMap3583_checked
#print axioms certified3583
def sourceMap3583swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3583swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3583swap_checked : acceptsGraphIso
    (source (graph core3583) (root 8) 6 0) DegreeTwoThreeSpectrum5519.graph sourceMap3583swap=true := by decide +kernel
theorem fusedMap3583swap_checked : acceptsGraphIso
    (fused (graph core3583) (root 8) 6 0) DegreeTwoThreeSpectrum5521.graph fusedMap3583swap=true := by decide +kernel
theorem certified3583swap : Certified (graph core3583) (root 8) 6 0 :=
  of_native_maps core3583 DegreeTwoThreeSpectrum5519.graph DegreeTwoThreeSpectrum5521.graph
    sourceMap3583swap fusedMap3583swap sourceMap3583swap_checked fusedMap3583swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3583
#print axioms sourceMap3583swap_checked
#print axioms fusedMap3583swap_checked
#print axioms certified3583swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
