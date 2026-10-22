/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2008 : Family 10 := level10.get ⟨1639,by decide⟩
def sourceMap2008 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2008 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2008_checked : acceptsGraphIso
    (source (graph core2008) (root 10) 0 2) DegreeTwoThreeSpectrum3795.graph sourceMap2008=true := by decide +kernel
theorem fusedMap2008_checked : acceptsGraphIso
    (fused (graph core2008) (root 10) 0 2) DegreeTwoThreeSpectrum3188.graph fusedMap2008=true := by decide +kernel
theorem certified2008 : Certified (graph core2008) (root 10) 0 2 :=
  of_native_maps core2008 DegreeTwoThreeSpectrum3795.graph DegreeTwoThreeSpectrum3188.graph
    sourceMap2008 fusedMap2008 sourceMap2008_checked fusedMap2008_checked
    DegreeTwoThreeFiniteComparisons.comparison2008
#print axioms sourceMap2008_checked
#print axioms fusedMap2008_checked
#print axioms certified2008
def sourceMap2008swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2008swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2008swap_checked : acceptsGraphIso
    (source (graph core2008) (root 10) 2 0) DegreeTwoThreeSpectrum3795.graph sourceMap2008swap=true := by decide +kernel
theorem fusedMap2008swap_checked : acceptsGraphIso
    (fused (graph core2008) (root 10) 2 0) DegreeTwoThreeSpectrum3188.graph fusedMap2008swap=true := by decide +kernel
theorem certified2008swap : Certified (graph core2008) (root 10) 2 0 :=
  of_native_maps core2008 DegreeTwoThreeSpectrum3795.graph DegreeTwoThreeSpectrum3188.graph
    sourceMap2008swap fusedMap2008swap sourceMap2008swap_checked fusedMap2008swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2008
#print axioms sourceMap2008swap_checked
#print axioms fusedMap2008swap_checked
#print axioms certified2008swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
