/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3580 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap3580 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3580 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3580_checked : acceptsGraphIso
    (source (graph core3580) (root 8) 0 6) DegreeTwoThreeSpectrum5461.graph sourceMap3580=true := by decide +kernel
theorem fusedMap3580_checked : acceptsGraphIso
    (fused (graph core3580) (root 8) 0 6) DegreeTwoThreeSpectrum5463.graph fusedMap3580=true := by decide +kernel
theorem certified3580 : Certified (graph core3580) (root 8) 0 6 :=
  of_native_maps core3580 DegreeTwoThreeSpectrum5461.graph DegreeTwoThreeSpectrum5463.graph
    sourceMap3580 fusedMap3580 sourceMap3580_checked fusedMap3580_checked
    DegreeTwoThreeFiniteComparisons.comparison3580
#print axioms sourceMap3580_checked
#print axioms fusedMap3580_checked
#print axioms certified3580
def sourceMap3580swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3580swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3580swap_checked : acceptsGraphIso
    (source (graph core3580) (root 8) 6 0) DegreeTwoThreeSpectrum5461.graph sourceMap3580swap=true := by decide +kernel
theorem fusedMap3580swap_checked : acceptsGraphIso
    (fused (graph core3580) (root 8) 6 0) DegreeTwoThreeSpectrum5463.graph fusedMap3580swap=true := by decide +kernel
theorem certified3580swap : Certified (graph core3580) (root 8) 6 0 :=
  of_native_maps core3580 DegreeTwoThreeSpectrum5461.graph DegreeTwoThreeSpectrum5463.graph
    sourceMap3580swap fusedMap3580swap sourceMap3580swap_checked fusedMap3580swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3580
#print axioms sourceMap3580swap_checked
#print axioms fusedMap3580swap_checked
#print axioms certified3580swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
