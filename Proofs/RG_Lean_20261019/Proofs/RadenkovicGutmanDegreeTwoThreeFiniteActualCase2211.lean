/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2211 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap2211 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2211 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2211_checked : acceptsGraphIso
    (source (graph core2211) (root 8) 0 4) DegreeTwoThreeSpectrum2998.graph sourceMap2211=true := by decide +kernel
theorem fusedMap2211_checked : acceptsGraphIso
    (fused (graph core2211) (root 8) 0 4) DegreeTwoThreeSpectrum3000.graph fusedMap2211=true := by decide +kernel
theorem certified2211 : Certified (graph core2211) (root 8) 0 4 :=
  of_native_maps core2211 DegreeTwoThreeSpectrum2998.graph DegreeTwoThreeSpectrum3000.graph
    sourceMap2211 fusedMap2211 sourceMap2211_checked fusedMap2211_checked
    DegreeTwoThreeFiniteComparisons.comparison2211
#print axioms sourceMap2211_checked
#print axioms fusedMap2211_checked
#print axioms certified2211
def sourceMap2211swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2211swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2211swap_checked : acceptsGraphIso
    (source (graph core2211) (root 8) 4 0) DegreeTwoThreeSpectrum2998.graph sourceMap2211swap=true := by decide +kernel
theorem fusedMap2211swap_checked : acceptsGraphIso
    (fused (graph core2211) (root 8) 4 0) DegreeTwoThreeSpectrum3000.graph fusedMap2211swap=true := by decide +kernel
theorem certified2211swap : Certified (graph core2211) (root 8) 4 0 :=
  of_native_maps core2211 DegreeTwoThreeSpectrum2998.graph DegreeTwoThreeSpectrum3000.graph
    sourceMap2211swap fusedMap2211swap sourceMap2211swap_checked fusedMap2211swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2211
#print axioms sourceMap2211swap_checked
#print axioms fusedMap2211swap_checked
#print axioms certified2211swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
