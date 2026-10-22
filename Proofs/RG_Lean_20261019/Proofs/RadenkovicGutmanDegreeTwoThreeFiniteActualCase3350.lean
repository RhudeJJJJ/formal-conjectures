/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3350 : Family 9 := level9.get ⟨372,by decide⟩
def sourceMap3350 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3350 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3350_checked : acceptsGraphIso
    (source (graph core3350) (root 9) 0 5) DegreeTwoThreeSpectrum6274.graph sourceMap3350=true := by decide +kernel
theorem fusedMap3350_checked : acceptsGraphIso
    (fused (graph core3350) (root 9) 0 5) DegreeTwoThreeSpectrum5255.graph fusedMap3350=true := by decide +kernel
theorem certified3350 : Certified (graph core3350) (root 9) 0 5 :=
  of_native_maps core3350 DegreeTwoThreeSpectrum6274.graph DegreeTwoThreeSpectrum5255.graph
    sourceMap3350 fusedMap3350 sourceMap3350_checked fusedMap3350_checked
    DegreeTwoThreeFiniteComparisons.comparison3350
#print axioms sourceMap3350_checked
#print axioms fusedMap3350_checked
#print axioms certified3350
def sourceMap3350swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3350swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3350swap_checked : acceptsGraphIso
    (source (graph core3350) (root 9) 5 0) DegreeTwoThreeSpectrum6274.graph sourceMap3350swap=true := by decide +kernel
theorem fusedMap3350swap_checked : acceptsGraphIso
    (fused (graph core3350) (root 9) 5 0) DegreeTwoThreeSpectrum5255.graph fusedMap3350swap=true := by decide +kernel
theorem certified3350swap : Certified (graph core3350) (root 9) 5 0 :=
  of_native_maps core3350 DegreeTwoThreeSpectrum6274.graph DegreeTwoThreeSpectrum5255.graph
    sourceMap3350swap fusedMap3350swap sourceMap3350swap_checked fusedMap3350swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3350
#print axioms sourceMap3350swap_checked
#print axioms fusedMap3350swap_checked
#print axioms certified3350swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
