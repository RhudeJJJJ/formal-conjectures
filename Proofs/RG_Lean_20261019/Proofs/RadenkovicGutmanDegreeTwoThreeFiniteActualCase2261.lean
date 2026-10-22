/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2261 : Family 9 := level9.get ⟨184,by decide⟩
def sourceMap2261 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2261 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2261_checked : acceptsGraphIso
    (source (graph core2261) (root 9) 0 4) DegreeTwoThreeSpectrum4365.graph sourceMap2261=true := by decide +kernel
theorem fusedMap2261_checked : acceptsGraphIso
    (fused (graph core2261) (root 9) 0 4) DegreeTwoThreeSpectrum3952.graph fusedMap2261=true := by decide +kernel
theorem certified2261 : Certified (graph core2261) (root 9) 0 4 :=
  of_native_maps core2261 DegreeTwoThreeSpectrum4365.graph DegreeTwoThreeSpectrum3952.graph
    sourceMap2261 fusedMap2261 sourceMap2261_checked fusedMap2261_checked
    DegreeTwoThreeFiniteComparisons.comparison2261
#print axioms sourceMap2261_checked
#print axioms fusedMap2261_checked
#print axioms certified2261
def sourceMap2261swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2261swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2261swap_checked : acceptsGraphIso
    (source (graph core2261) (root 9) 4 0) DegreeTwoThreeSpectrum4365.graph sourceMap2261swap=true := by decide +kernel
theorem fusedMap2261swap_checked : acceptsGraphIso
    (fused (graph core2261) (root 9) 4 0) DegreeTwoThreeSpectrum3952.graph fusedMap2261swap=true := by decide +kernel
theorem certified2261swap : Certified (graph core2261) (root 9) 4 0 :=
  of_native_maps core2261 DegreeTwoThreeSpectrum4365.graph DegreeTwoThreeSpectrum3952.graph
    sourceMap2261swap fusedMap2261swap sourceMap2261swap_checked fusedMap2261swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2261
#print axioms sourceMap2261swap_checked
#print axioms fusedMap2261swap_checked
#print axioms certified2261swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
