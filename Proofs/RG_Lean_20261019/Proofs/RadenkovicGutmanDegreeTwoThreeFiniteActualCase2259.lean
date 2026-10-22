/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2259 : Family 9 := level9.get ⟨178,by decide⟩
def sourceMap2259 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2259 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2259_checked : acceptsGraphIso
    (source (graph core2259) (root 9) 0 4) DegreeTwoThreeSpectrum4352.graph sourceMap2259=true := by decide +kernel
theorem fusedMap2259_checked : acceptsGraphIso
    (fused (graph core2259) (root 9) 0 4) DegreeTwoThreeSpectrum3945.graph fusedMap2259=true := by decide +kernel
theorem certified2259 : Certified (graph core2259) (root 9) 0 4 :=
  of_native_maps core2259 DegreeTwoThreeSpectrum4352.graph DegreeTwoThreeSpectrum3945.graph
    sourceMap2259 fusedMap2259 sourceMap2259_checked fusedMap2259_checked
    DegreeTwoThreeFiniteComparisons.comparison2259
#print axioms sourceMap2259_checked
#print axioms fusedMap2259_checked
#print axioms certified2259
def sourceMap2259swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2259swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2259swap_checked : acceptsGraphIso
    (source (graph core2259) (root 9) 4 0) DegreeTwoThreeSpectrum4352.graph sourceMap2259swap=true := by decide +kernel
theorem fusedMap2259swap_checked : acceptsGraphIso
    (fused (graph core2259) (root 9) 4 0) DegreeTwoThreeSpectrum3945.graph fusedMap2259swap=true := by decide +kernel
theorem certified2259swap : Certified (graph core2259) (root 9) 4 0 :=
  of_native_maps core2259 DegreeTwoThreeSpectrum4352.graph DegreeTwoThreeSpectrum3945.graph
    sourceMap2259swap fusedMap2259swap sourceMap2259swap_checked fusedMap2259swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2259
#print axioms sourceMap2259swap_checked
#print axioms fusedMap2259swap_checked
#print axioms certified2259swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
