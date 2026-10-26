/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3558 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap3558 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3558 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3558_checked : acceptsGraphIso
    (source (graph core3558) (root 8) 0 6) DegreeTwoThreeSpectrum5787.graph sourceMap3558=true := by decide +kernel
theorem fusedMap3558_checked : acceptsGraphIso
    (fused (graph core3558) (root 8) 0 6) DegreeTwoThreeSpectrum5063.graph fusedMap3558=true := by decide +kernel
theorem certified3558 : Certified (graph core3558) (root 8) 0 6 :=
  of_native_maps core3558 DegreeTwoThreeSpectrum5787.graph DegreeTwoThreeSpectrum5063.graph
    sourceMap3558 fusedMap3558 sourceMap3558_checked fusedMap3558_checked
    DegreeTwoThreeFiniteComparisons.comparison3558
#print axioms sourceMap3558_checked
#print axioms fusedMap3558_checked
#print axioms certified3558
def sourceMap3558swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3558swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3558swap_checked : acceptsGraphIso
    (source (graph core3558) (root 8) 6 0) DegreeTwoThreeSpectrum5787.graph sourceMap3558swap=true := by decide +kernel
theorem fusedMap3558swap_checked : acceptsGraphIso
    (fused (graph core3558) (root 8) 6 0) DegreeTwoThreeSpectrum5063.graph fusedMap3558swap=true := by decide +kernel
theorem certified3558swap : Certified (graph core3558) (root 8) 6 0 :=
  of_native_maps core3558 DegreeTwoThreeSpectrum5787.graph DegreeTwoThreeSpectrum5063.graph
    sourceMap3558swap fusedMap3558swap sourceMap3558swap_checked fusedMap3558swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3558
#print axioms sourceMap3558swap_checked
#print axioms fusedMap3558swap_checked
#print axioms certified3558swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
