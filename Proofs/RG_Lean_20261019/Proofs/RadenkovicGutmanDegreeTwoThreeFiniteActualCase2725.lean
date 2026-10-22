/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2725 : Family 10 := level10.get ⟨888,by decide⟩
def sourceMap2725 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2725 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2725_checked : acceptsGraphIso
    (source (graph core2725) (root 10) 0 4) DegreeTwoThreeSpectrum6956.graph sourceMap2725=true := by decide +kernel
theorem fusedMap2725_checked : acceptsGraphIso
    (fused (graph core2725) (root 10) 0 4) DegreeTwoThreeSpectrum5742.graph fusedMap2725=true := by decide +kernel
theorem certified2725 : Certified (graph core2725) (root 10) 0 4 :=
  of_native_maps core2725 DegreeTwoThreeSpectrum6956.graph DegreeTwoThreeSpectrum5742.graph
    sourceMap2725 fusedMap2725 sourceMap2725_checked fusedMap2725_checked
    DegreeTwoThreeFiniteComparisons.comparison2725
#print axioms sourceMap2725_checked
#print axioms fusedMap2725_checked
#print axioms certified2725
def sourceMap2725swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2725swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2725swap_checked : acceptsGraphIso
    (source (graph core2725) (root 10) 4 0) DegreeTwoThreeSpectrum6956.graph sourceMap2725swap=true := by decide +kernel
theorem fusedMap2725swap_checked : acceptsGraphIso
    (fused (graph core2725) (root 10) 4 0) DegreeTwoThreeSpectrum5742.graph fusedMap2725swap=true := by decide +kernel
theorem certified2725swap : Certified (graph core2725) (root 10) 4 0 :=
  of_native_maps core2725 DegreeTwoThreeSpectrum6956.graph DegreeTwoThreeSpectrum5742.graph
    sourceMap2725swap fusedMap2725swap sourceMap2725swap_checked fusedMap2725swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2725
#print axioms sourceMap2725swap_checked
#print axioms fusedMap2725swap_checked
#print axioms certified2725swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
