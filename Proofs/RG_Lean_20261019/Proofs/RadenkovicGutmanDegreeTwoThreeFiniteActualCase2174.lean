/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2174 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap2174 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2174 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2174_checked : acceptsGraphIso
    (source (graph core2174) (root 8) 0 4) DegreeTwoThreeSpectrum2881.graph sourceMap2174=true := by decide +kernel
theorem fusedMap2174_checked : acceptsGraphIso
    (fused (graph core2174) (root 8) 0 4) DegreeTwoThreeSpectrum2884.graph fusedMap2174=true := by decide +kernel
theorem certified2174 : Certified (graph core2174) (root 8) 0 4 :=
  of_native_maps core2174 DegreeTwoThreeSpectrum2881.graph DegreeTwoThreeSpectrum2884.graph
    sourceMap2174 fusedMap2174 sourceMap2174_checked fusedMap2174_checked
    DegreeTwoThreeFiniteComparisons.comparison2174
#print axioms sourceMap2174_checked
#print axioms fusedMap2174_checked
#print axioms certified2174
def sourceMap2174swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2174swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2174swap_checked : acceptsGraphIso
    (source (graph core2174) (root 8) 4 0) DegreeTwoThreeSpectrum2881.graph sourceMap2174swap=true := by decide +kernel
theorem fusedMap2174swap_checked : acceptsGraphIso
    (fused (graph core2174) (root 8) 4 0) DegreeTwoThreeSpectrum2884.graph fusedMap2174swap=true := by decide +kernel
theorem certified2174swap : Certified (graph core2174) (root 8) 4 0 :=
  of_native_maps core2174 DegreeTwoThreeSpectrum2881.graph DegreeTwoThreeSpectrum2884.graph
    sourceMap2174swap fusedMap2174swap sourceMap2174swap_checked fusedMap2174swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2174
#print axioms sourceMap2174swap_checked
#print axioms fusedMap2174swap_checked
#print axioms certified2174swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
