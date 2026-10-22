/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3293 : Family 9 := level9.get ⟨216,by decide⟩
def sourceMap3293 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3293 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3293_checked : acceptsGraphIso
    (source (graph core3293) (root 9) 0 5) DegreeTwoThreeSpectrum5495.graph sourceMap3293=true := by decide +kernel
theorem fusedMap3293_checked : acceptsGraphIso
    (fused (graph core3293) (root 9) 0 5) DegreeTwoThreeSpectrum5496.graph fusedMap3293=true := by decide +kernel
theorem certified3293 : Certified (graph core3293) (root 9) 0 5 :=
  of_native_maps core3293 DegreeTwoThreeSpectrum5495.graph DegreeTwoThreeSpectrum5496.graph
    sourceMap3293 fusedMap3293 sourceMap3293_checked fusedMap3293_checked
    DegreeTwoThreeFiniteComparisons.comparison3293
#print axioms sourceMap3293_checked
#print axioms fusedMap3293_checked
#print axioms certified3293
def sourceMap3293swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3293swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3293swap_checked : acceptsGraphIso
    (source (graph core3293) (root 9) 5 0) DegreeTwoThreeSpectrum5495.graph sourceMap3293swap=true := by decide +kernel
theorem fusedMap3293swap_checked : acceptsGraphIso
    (fused (graph core3293) (root 9) 5 0) DegreeTwoThreeSpectrum5496.graph fusedMap3293swap=true := by decide +kernel
theorem certified3293swap : Certified (graph core3293) (root 9) 5 0 :=
  of_native_maps core3293 DegreeTwoThreeSpectrum5495.graph DegreeTwoThreeSpectrum5496.graph
    sourceMap3293swap fusedMap3293swap sourceMap3293swap_checked fusedMap3293swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3293
#print axioms sourceMap3293swap_checked
#print axioms fusedMap3293swap_checked
#print axioms certified3293swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
