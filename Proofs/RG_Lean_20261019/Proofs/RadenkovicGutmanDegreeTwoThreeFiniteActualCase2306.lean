/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2306 : Family 9 := level9.get ⟨308,by decide⟩
def sourceMap2306 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10] (sourceLabel 9 0 4 v)
def fusedMap2306 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2306_checked : acceptsGraphIso
    (source (graph core2306) (root 9) 0 4) DegreeTwoThreeSpectrum4658.graph sourceMap2306=true := by decide +kernel
theorem fusedMap2306_checked : acceptsGraphIso
    (fused (graph core2306) (root 9) 0 4) DegreeTwoThreeSpectrum4150.graph fusedMap2306=true := by decide +kernel
theorem certified2306 : Certified (graph core2306) (root 9) 0 4 :=
  of_native_maps core2306 DegreeTwoThreeSpectrum4658.graph DegreeTwoThreeSpectrum4150.graph
    sourceMap2306 fusedMap2306 sourceMap2306_checked fusedMap2306_checked
    DegreeTwoThreeFiniteComparisons.comparison2306
#print axioms sourceMap2306_checked
#print axioms fusedMap2306_checked
#print axioms certified2306
def sourceMap2306swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,6,7,8,9,10,15] (sourceLabel 9 4 0 v)
def fusedMap2306swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2306swap_checked : acceptsGraphIso
    (source (graph core2306) (root 9) 4 0) DegreeTwoThreeSpectrum4658.graph sourceMap2306swap=true := by decide +kernel
theorem fusedMap2306swap_checked : acceptsGraphIso
    (fused (graph core2306) (root 9) 4 0) DegreeTwoThreeSpectrum4150.graph fusedMap2306swap=true := by decide +kernel
theorem certified2306swap : Certified (graph core2306) (root 9) 4 0 :=
  of_native_maps core2306 DegreeTwoThreeSpectrum4658.graph DegreeTwoThreeSpectrum4150.graph
    sourceMap2306swap fusedMap2306swap sourceMap2306swap_checked fusedMap2306swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2306
#print axioms sourceMap2306swap_checked
#print axioms fusedMap2306swap_checked
#print axioms certified2306swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
