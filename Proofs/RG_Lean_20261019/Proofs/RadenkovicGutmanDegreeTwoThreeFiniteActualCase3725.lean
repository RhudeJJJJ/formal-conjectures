/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3725 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap3725 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3725 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3725_checked : acceptsGraphIso
    (source (graph core3725) (root 6) 0 8) DegreeTwoThreeSpectrum5224.graph sourceMap3725=true := by decide +kernel
theorem fusedMap3725_checked : acceptsGraphIso
    (fused (graph core3725) (root 6) 0 8) DegreeTwoThreeSpectrum5228.graph fusedMap3725=true := by decide +kernel
theorem certified3725 : Certified (graph core3725) (root 6) 0 8 :=
  of_native_maps core3725 DegreeTwoThreeSpectrum5224.graph DegreeTwoThreeSpectrum5228.graph
    sourceMap3725 fusedMap3725 sourceMap3725_checked fusedMap3725_checked
    DegreeTwoThreeFiniteComparisons.comparison3725
#print axioms sourceMap3725_checked
#print axioms fusedMap3725_checked
#print axioms certified3725
def sourceMap3725swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3725swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3725swap_checked : acceptsGraphIso
    (source (graph core3725) (root 6) 8 0) DegreeTwoThreeSpectrum5224.graph sourceMap3725swap=true := by decide +kernel
theorem fusedMap3725swap_checked : acceptsGraphIso
    (fused (graph core3725) (root 6) 8 0) DegreeTwoThreeSpectrum5228.graph fusedMap3725swap=true := by decide +kernel
theorem certified3725swap : Certified (graph core3725) (root 6) 8 0 :=
  of_native_maps core3725 DegreeTwoThreeSpectrum5224.graph DegreeTwoThreeSpectrum5228.graph
    sourceMap3725swap fusedMap3725swap sourceMap3725swap_checked fusedMap3725swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3725
#print axioms sourceMap3725swap_checked
#print axioms fusedMap3725swap_checked
#print axioms certified3725swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
