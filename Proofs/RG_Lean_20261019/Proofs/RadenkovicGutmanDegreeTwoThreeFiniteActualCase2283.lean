/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2283 : Family 9 := level9.get ⟨247,by decide⟩
def sourceMap2283 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2283 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2283_checked : acceptsGraphIso
    (source (graph core2283) (root 9) 0 4) DegreeTwoThreeSpectrum4536.graph sourceMap2283=true := by decide +kernel
theorem fusedMap2283_checked : acceptsGraphIso
    (fused (graph core2283) (root 9) 0 4) DegreeTwoThreeSpectrum4048.graph fusedMap2283=true := by decide +kernel
theorem certified2283 : Certified (graph core2283) (root 9) 0 4 :=
  of_native_maps core2283 DegreeTwoThreeSpectrum4536.graph DegreeTwoThreeSpectrum4048.graph
    sourceMap2283 fusedMap2283 sourceMap2283_checked fusedMap2283_checked
    DegreeTwoThreeFiniteComparisons.comparison2283
#print axioms sourceMap2283_checked
#print axioms fusedMap2283_checked
#print axioms certified2283
def sourceMap2283swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2283swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2283swap_checked : acceptsGraphIso
    (source (graph core2283) (root 9) 4 0) DegreeTwoThreeSpectrum4536.graph sourceMap2283swap=true := by decide +kernel
theorem fusedMap2283swap_checked : acceptsGraphIso
    (fused (graph core2283) (root 9) 4 0) DegreeTwoThreeSpectrum4048.graph fusedMap2283swap=true := by decide +kernel
theorem certified2283swap : Certified (graph core2283) (root 9) 4 0 :=
  of_native_maps core2283 DegreeTwoThreeSpectrum4536.graph DegreeTwoThreeSpectrum4048.graph
    sourceMap2283swap fusedMap2283swap sourceMap2283swap_checked fusedMap2283swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2283
#print axioms sourceMap2283swap_checked
#print axioms fusedMap2283swap_checked
#print axioms certified2283swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
