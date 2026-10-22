/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2113 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap2113 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2113 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2113_checked : acceptsGraphIso
    (source (graph core2113) (root 7) 0 4) DegreeTwoThreeSpectrum2143.graph sourceMap2113=true := by decide +kernel
theorem fusedMap2113_checked : acceptsGraphIso
    (fused (graph core2113) (root 7) 0 4) DegreeTwoThreeSpectrum1830.graph fusedMap2113=true := by decide +kernel
theorem certified2113 : Certified (graph core2113) (root 7) 0 4 :=
  of_native_maps core2113 DegreeTwoThreeSpectrum2143.graph DegreeTwoThreeSpectrum1830.graph
    sourceMap2113 fusedMap2113 sourceMap2113_checked fusedMap2113_checked
    DegreeTwoThreeFiniteComparisons.comparison2113
#print axioms sourceMap2113_checked
#print axioms fusedMap2113_checked
#print axioms certified2113
def sourceMap2113swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2113swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2113swap_checked : acceptsGraphIso
    (source (graph core2113) (root 7) 4 0) DegreeTwoThreeSpectrum2143.graph sourceMap2113swap=true := by decide +kernel
theorem fusedMap2113swap_checked : acceptsGraphIso
    (fused (graph core2113) (root 7) 4 0) DegreeTwoThreeSpectrum1830.graph fusedMap2113swap=true := by decide +kernel
theorem certified2113swap : Certified (graph core2113) (root 7) 4 0 :=
  of_native_maps core2113 DegreeTwoThreeSpectrum2143.graph DegreeTwoThreeSpectrum1830.graph
    sourceMap2113swap fusedMap2113swap sourceMap2113swap_checked fusedMap2113swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2113
#print axioms sourceMap2113swap_checked
#print axioms fusedMap2113swap_checked
#print axioms certified2113swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
