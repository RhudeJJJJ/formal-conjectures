/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2125 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap2125 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,6,7,8,1,2,3,4,5] (sourceLabel 8 0 4 v)
def fusedMap2125 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (fusedLabel 8 0 4 v)
theorem sourceMap2125_checked : acceptsGraphIso
    (source (graph core2125) (root 8) 0 4) DegreeTwoThreeSpectrum2430.graph sourceMap2125=true := by decide +kernel
theorem fusedMap2125_checked : acceptsGraphIso
    (fused (graph core2125) (root 8) 0 4) DegreeTwoThreeSpectrum2435.graph fusedMap2125=true := by decide +kernel
theorem certified2125 : Certified (graph core2125) (root 8) 0 4 :=
  of_native_maps core2125 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2435.graph
    sourceMap2125 fusedMap2125 sourceMap2125_checked fusedMap2125_checked
    DegreeTwoThreeFiniteComparisons.comparison2125
#print axioms sourceMap2125_checked
#print axioms fusedMap2125_checked
#print axioms certified2125
def sourceMap2125swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,6,7,1,2,3,4,5,8] (sourceLabel 8 4 0 v)
def fusedMap2125swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (fusedLabel 8 4 0 v)
theorem sourceMap2125swap_checked : acceptsGraphIso
    (source (graph core2125) (root 8) 4 0) DegreeTwoThreeSpectrum2430.graph sourceMap2125swap=true := by decide +kernel
theorem fusedMap2125swap_checked : acceptsGraphIso
    (fused (graph core2125) (root 8) 4 0) DegreeTwoThreeSpectrum2435.graph fusedMap2125swap=true := by decide +kernel
theorem certified2125swap : Certified (graph core2125) (root 8) 4 0 :=
  of_native_maps core2125 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2435.graph
    sourceMap2125swap fusedMap2125swap sourceMap2125swap_checked fusedMap2125swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2125
#print axioms sourceMap2125swap_checked
#print axioms fusedMap2125swap_checked
#print axioms certified2125swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
