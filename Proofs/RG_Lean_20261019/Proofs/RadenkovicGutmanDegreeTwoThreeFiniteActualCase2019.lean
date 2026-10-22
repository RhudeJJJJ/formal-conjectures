/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2019 : Family 10 := level10.get ⟨1665,by decide⟩
def sourceMap2019 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2019 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2019_checked : acceptsGraphIso
    (source (graph core2019) (root 10) 0 2) DegreeTwoThreeSpectrum3808.graph sourceMap2019=true := by decide +kernel
theorem fusedMap2019_checked : acceptsGraphIso
    (fused (graph core2019) (root 10) 0 2) DegreeTwoThreeSpectrum3237.graph fusedMap2019=true := by decide +kernel
theorem certified2019 : Certified (graph core2019) (root 10) 0 2 :=
  of_native_maps core2019 DegreeTwoThreeSpectrum3808.graph DegreeTwoThreeSpectrum3237.graph
    sourceMap2019 fusedMap2019 sourceMap2019_checked fusedMap2019_checked
    DegreeTwoThreeFiniteComparisons.comparison2019
#print axioms sourceMap2019_checked
#print axioms fusedMap2019_checked
#print axioms certified2019
def sourceMap2019swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2019swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2019swap_checked : acceptsGraphIso
    (source (graph core2019) (root 10) 2 0) DegreeTwoThreeSpectrum3808.graph sourceMap2019swap=true := by decide +kernel
theorem fusedMap2019swap_checked : acceptsGraphIso
    (fused (graph core2019) (root 10) 2 0) DegreeTwoThreeSpectrum3237.graph fusedMap2019swap=true := by decide +kernel
theorem certified2019swap : Certified (graph core2019) (root 10) 2 0 :=
  of_native_maps core2019 DegreeTwoThreeSpectrum3808.graph DegreeTwoThreeSpectrum3237.graph
    sourceMap2019swap fusedMap2019swap sourceMap2019swap_checked fusedMap2019swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2019
#print axioms sourceMap2019swap_checked
#print axioms fusedMap2019swap_checked
#print axioms certified2019swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
