/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2035 : Family 10 := level10.get ⟨1724,by decide⟩
def sourceMap2035 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2035 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2035_checked : acceptsGraphIso
    (source (graph core2035) (root 10) 0 2) DegreeTwoThreeSpectrum3830.graph sourceMap2035=true := by decide +kernel
theorem fusedMap2035_checked : acceptsGraphIso
    (fused (graph core2035) (root 10) 0 2) DegreeTwoThreeSpectrum3418.graph fusedMap2035=true := by decide +kernel
theorem certified2035 : Certified (graph core2035) (root 10) 0 2 :=
  of_native_maps core2035 DegreeTwoThreeSpectrum3830.graph DegreeTwoThreeSpectrum3418.graph
    sourceMap2035 fusedMap2035 sourceMap2035_checked fusedMap2035_checked
    DegreeTwoThreeFiniteComparisons.comparison2035
#print axioms sourceMap2035_checked
#print axioms fusedMap2035_checked
#print axioms certified2035
def sourceMap2035swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2035swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2035swap_checked : acceptsGraphIso
    (source (graph core2035) (root 10) 2 0) DegreeTwoThreeSpectrum3830.graph sourceMap2035swap=true := by decide +kernel
theorem fusedMap2035swap_checked : acceptsGraphIso
    (fused (graph core2035) (root 10) 2 0) DegreeTwoThreeSpectrum3418.graph fusedMap2035swap=true := by decide +kernel
theorem certified2035swap : Certified (graph core2035) (root 10) 2 0 :=
  of_native_maps core2035 DegreeTwoThreeSpectrum3830.graph DegreeTwoThreeSpectrum3418.graph
    sourceMap2035swap fusedMap2035swap sourceMap2035swap_checked fusedMap2035swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2035
#print axioms sourceMap2035swap_checked
#print axioms fusedMap2035swap_checked
#print axioms certified2035swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
