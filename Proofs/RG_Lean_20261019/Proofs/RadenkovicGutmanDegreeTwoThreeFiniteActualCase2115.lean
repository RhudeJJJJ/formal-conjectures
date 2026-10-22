/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2115 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap2115 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2115 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2115_checked : acceptsGraphIso
    (source (graph core2115) (root 7) 0 4) DegreeTwoThreeSpectrum2193.graph sourceMap2115=true := by decide +kernel
theorem fusedMap2115_checked : acceptsGraphIso
    (fused (graph core2115) (root 7) 0 4) DegreeTwoThreeSpectrum1862.graph fusedMap2115=true := by decide +kernel
theorem certified2115 : Certified (graph core2115) (root 7) 0 4 :=
  of_native_maps core2115 DegreeTwoThreeSpectrum2193.graph DegreeTwoThreeSpectrum1862.graph
    sourceMap2115 fusedMap2115 sourceMap2115_checked fusedMap2115_checked
    DegreeTwoThreeFiniteComparisons.comparison2115
#print axioms sourceMap2115_checked
#print axioms fusedMap2115_checked
#print axioms certified2115
def sourceMap2115swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2115swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2115swap_checked : acceptsGraphIso
    (source (graph core2115) (root 7) 4 0) DegreeTwoThreeSpectrum2193.graph sourceMap2115swap=true := by decide +kernel
theorem fusedMap2115swap_checked : acceptsGraphIso
    (fused (graph core2115) (root 7) 4 0) DegreeTwoThreeSpectrum1862.graph fusedMap2115swap=true := by decide +kernel
theorem certified2115swap : Certified (graph core2115) (root 7) 4 0 :=
  of_native_maps core2115 DegreeTwoThreeSpectrum2193.graph DegreeTwoThreeSpectrum1862.graph
    sourceMap2115swap fusedMap2115swap sourceMap2115swap_checked fusedMap2115swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2115
#print axioms sourceMap2115swap_checked
#print axioms fusedMap2115swap_checked
#print axioms certified2115swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
