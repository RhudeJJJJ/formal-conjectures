/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2320 : Family 9 := level9.get ⟨348,by decide⟩
def sourceMap2320 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2320 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2320_checked : acceptsGraphIso
    (source (graph core2320) (root 9) 0 4) DegreeTwoThreeSpectrum4246.graph sourceMap2320=true := by decide +kernel
theorem fusedMap2320_checked : acceptsGraphIso
    (fused (graph core2320) (root 9) 0 4) DegreeTwoThreeSpectrum4247.graph fusedMap2320=true := by decide +kernel
theorem certified2320 : Certified (graph core2320) (root 9) 0 4 :=
  of_native_maps core2320 DegreeTwoThreeSpectrum4246.graph DegreeTwoThreeSpectrum4247.graph
    sourceMap2320 fusedMap2320 sourceMap2320_checked fusedMap2320_checked
    DegreeTwoThreeFiniteComparisons.comparison2320
#print axioms sourceMap2320_checked
#print axioms fusedMap2320_checked
#print axioms certified2320
def sourceMap2320swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2320swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2320swap_checked : acceptsGraphIso
    (source (graph core2320) (root 9) 4 0) DegreeTwoThreeSpectrum4246.graph sourceMap2320swap=true := by decide +kernel
theorem fusedMap2320swap_checked : acceptsGraphIso
    (fused (graph core2320) (root 9) 4 0) DegreeTwoThreeSpectrum4247.graph fusedMap2320swap=true := by decide +kernel
theorem certified2320swap : Certified (graph core2320) (root 9) 4 0 :=
  of_native_maps core2320 DegreeTwoThreeSpectrum4246.graph DegreeTwoThreeSpectrum4247.graph
    sourceMap2320swap fusedMap2320swap sourceMap2320swap_checked fusedMap2320swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2320
#print axioms sourceMap2320swap_checked
#print axioms fusedMap2320swap_checked
#print axioms certified2320swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
