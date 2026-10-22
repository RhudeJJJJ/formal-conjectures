/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2020 : Family 10 := level10.get ⟨1669,by decide⟩
def sourceMap2020 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap2020 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2020_checked : acceptsGraphIso
    (source (graph core2020) (root 10) 0 2) DegreeTwoThreeSpectrum3811.graph sourceMap2020=true := by decide +kernel
theorem fusedMap2020_checked : acceptsGraphIso
    (fused (graph core2020) (root 10) 0 2) DegreeTwoThreeSpectrum3244.graph fusedMap2020=true := by decide +kernel
theorem certified2020 : Certified (graph core2020) (root 10) 0 2 :=
  of_native_maps core2020 DegreeTwoThreeSpectrum3811.graph DegreeTwoThreeSpectrum3244.graph
    sourceMap2020 fusedMap2020 sourceMap2020_checked fusedMap2020_checked
    DegreeTwoThreeFiniteComparisons.comparison2020
#print axioms sourceMap2020_checked
#print axioms fusedMap2020_checked
#print axioms certified2020
def sourceMap2020swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8,14] (sourceLabel 10 2 0 v)
def fusedMap2020swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2020swap_checked : acceptsGraphIso
    (source (graph core2020) (root 10) 2 0) DegreeTwoThreeSpectrum3811.graph sourceMap2020swap=true := by decide +kernel
theorem fusedMap2020swap_checked : acceptsGraphIso
    (fused (graph core2020) (root 10) 2 0) DegreeTwoThreeSpectrum3244.graph fusedMap2020swap=true := by decide +kernel
theorem certified2020swap : Certified (graph core2020) (root 10) 2 0 :=
  of_native_maps core2020 DegreeTwoThreeSpectrum3811.graph DegreeTwoThreeSpectrum3244.graph
    sourceMap2020swap fusedMap2020swap sourceMap2020swap_checked fusedMap2020swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2020
#print axioms sourceMap2020swap_checked
#print axioms fusedMap2020swap_checked
#print axioms certified2020swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
