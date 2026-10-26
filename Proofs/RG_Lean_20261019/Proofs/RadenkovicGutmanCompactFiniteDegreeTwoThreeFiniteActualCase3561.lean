/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3561 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap3561 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3561 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3561_checked : acceptsGraphIso
    (source (graph core3561) (root 8) 0 6) DegreeTwoThreeSpectrum5878.graph sourceMap3561=true := by decide +kernel
theorem fusedMap3561_checked : acceptsGraphIso
    (fused (graph core3561) (root 8) 0 6) DegreeTwoThreeSpectrum5088.graph fusedMap3561=true := by decide +kernel
theorem certified3561 : Certified (graph core3561) (root 8) 0 6 :=
  of_native_maps core3561 DegreeTwoThreeSpectrum5878.graph DegreeTwoThreeSpectrum5088.graph
    sourceMap3561 fusedMap3561 sourceMap3561_checked fusedMap3561_checked
    DegreeTwoThreeFiniteComparisons.comparison3561
#print axioms sourceMap3561_checked
#print axioms fusedMap3561_checked
#print axioms certified3561
def sourceMap3561swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3561swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3561swap_checked : acceptsGraphIso
    (source (graph core3561) (root 8) 6 0) DegreeTwoThreeSpectrum5878.graph sourceMap3561swap=true := by decide +kernel
theorem fusedMap3561swap_checked : acceptsGraphIso
    (fused (graph core3561) (root 8) 6 0) DegreeTwoThreeSpectrum5088.graph fusedMap3561swap=true := by decide +kernel
theorem certified3561swap : Certified (graph core3561) (root 8) 6 0 :=
  of_native_maps core3561 DegreeTwoThreeSpectrum5878.graph DegreeTwoThreeSpectrum5088.graph
    sourceMap3561swap fusedMap3561swap sourceMap3561swap_checked fusedMap3561swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3561
#print axioms sourceMap3561swap_checked
#print axioms fusedMap3561swap_checked
#print axioms certified3561swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
