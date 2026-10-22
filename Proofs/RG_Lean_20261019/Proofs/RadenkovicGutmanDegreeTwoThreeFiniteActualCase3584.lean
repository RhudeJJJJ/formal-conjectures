/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3584 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap3584 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3584 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3584_checked : acceptsGraphIso
    (source (graph core3584) (root 8) 0 6) DegreeTwoThreeSpectrum5554.graph sourceMap3584=true := by decide +kernel
theorem fusedMap3584_checked : acceptsGraphIso
    (fused (graph core3584) (root 8) 0 6) DegreeTwoThreeSpectrum5556.graph fusedMap3584=true := by decide +kernel
theorem certified3584 : Certified (graph core3584) (root 8) 0 6 :=
  of_native_maps core3584 DegreeTwoThreeSpectrum5554.graph DegreeTwoThreeSpectrum5556.graph
    sourceMap3584 fusedMap3584 sourceMap3584_checked fusedMap3584_checked
    DegreeTwoThreeFiniteComparisons.comparison3584
#print axioms sourceMap3584_checked
#print axioms fusedMap3584_checked
#print axioms certified3584
def sourceMap3584swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3584swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3584swap_checked : acceptsGraphIso
    (source (graph core3584) (root 8) 6 0) DegreeTwoThreeSpectrum5554.graph sourceMap3584swap=true := by decide +kernel
theorem fusedMap3584swap_checked : acceptsGraphIso
    (fused (graph core3584) (root 8) 6 0) DegreeTwoThreeSpectrum5556.graph fusedMap3584swap=true := by decide +kernel
theorem certified3584swap : Certified (graph core3584) (root 8) 6 0 :=
  of_native_maps core3584 DegreeTwoThreeSpectrum5554.graph DegreeTwoThreeSpectrum5556.graph
    sourceMap3584swap fusedMap3584swap sourceMap3584swap_checked fusedMap3584swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3584
#print axioms sourceMap3584swap_checked
#print axioms fusedMap3584swap_checked
#print axioms certified3584swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
