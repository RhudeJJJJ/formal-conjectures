/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2030 : Family 10 := level10.get ⟨1711,by decide⟩
def sourceMap2030 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap2030 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2030_checked : acceptsGraphIso
    (source (graph core2030) (root 10) 0 2) DegreeTwoThreeSpectrum3824.graph sourceMap2030=true := by decide +kernel
theorem fusedMap2030_checked : acceptsGraphIso
    (fused (graph core2030) (root 10) 0 2) DegreeTwoThreeSpectrum3390.graph fusedMap2030=true := by decide +kernel
theorem certified2030 : Certified (graph core2030) (root 10) 0 2 :=
  of_native_maps core2030 DegreeTwoThreeSpectrum3824.graph DegreeTwoThreeSpectrum3390.graph
    sourceMap2030 fusedMap2030 sourceMap2030_checked fusedMap2030_checked
    DegreeTwoThreeFiniteComparisons.comparison2030
#print axioms sourceMap2030_checked
#print axioms fusedMap2030_checked
#print axioms certified2030
def sourceMap2030swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap2030swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2030swap_checked : acceptsGraphIso
    (source (graph core2030) (root 10) 2 0) DegreeTwoThreeSpectrum3824.graph sourceMap2030swap=true := by decide +kernel
theorem fusedMap2030swap_checked : acceptsGraphIso
    (fused (graph core2030) (root 10) 2 0) DegreeTwoThreeSpectrum3390.graph fusedMap2030swap=true := by decide +kernel
theorem certified2030swap : Certified (graph core2030) (root 10) 2 0 :=
  of_native_maps core2030 DegreeTwoThreeSpectrum3824.graph DegreeTwoThreeSpectrum3390.graph
    sourceMap2030swap fusedMap2030swap sourceMap2030swap_checked fusedMap2030swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2030
#print axioms sourceMap2030swap_checked
#print axioms fusedMap2030swap_checked
#print axioms certified2030swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
