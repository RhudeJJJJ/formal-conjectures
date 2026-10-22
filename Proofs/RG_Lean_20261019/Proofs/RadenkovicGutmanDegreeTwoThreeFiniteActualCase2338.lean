/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2338 : Family 9 := level9.get ⟨396,by decide⟩
def sourceMap2338 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2338 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2338_checked : acceptsGraphIso
    (source (graph core2338) (root 9) 0 4) DegreeTwoThreeSpectrum4349.graph sourceMap2338=true := by decide +kernel
theorem fusedMap2338_checked : acceptsGraphIso
    (fused (graph core2338) (root 9) 0 4) DegreeTwoThreeSpectrum4350.graph fusedMap2338=true := by decide +kernel
theorem certified2338 : Certified (graph core2338) (root 9) 0 4 :=
  of_native_maps core2338 DegreeTwoThreeSpectrum4349.graph DegreeTwoThreeSpectrum4350.graph
    sourceMap2338 fusedMap2338 sourceMap2338_checked fusedMap2338_checked
    DegreeTwoThreeFiniteComparisons.comparison2338
#print axioms sourceMap2338_checked
#print axioms fusedMap2338_checked
#print axioms certified2338
def sourceMap2338swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2338swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2338swap_checked : acceptsGraphIso
    (source (graph core2338) (root 9) 4 0) DegreeTwoThreeSpectrum4349.graph sourceMap2338swap=true := by decide +kernel
theorem fusedMap2338swap_checked : acceptsGraphIso
    (fused (graph core2338) (root 9) 4 0) DegreeTwoThreeSpectrum4350.graph fusedMap2338swap=true := by decide +kernel
theorem certified2338swap : Certified (graph core2338) (root 9) 4 0 :=
  of_native_maps core2338 DegreeTwoThreeSpectrum4349.graph DegreeTwoThreeSpectrum4350.graph
    sourceMap2338swap fusedMap2338swap sourceMap2338swap_checked fusedMap2338swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2338
#print axioms sourceMap2338swap_checked
#print axioms fusedMap2338swap_checked
#print axioms certified2338swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
