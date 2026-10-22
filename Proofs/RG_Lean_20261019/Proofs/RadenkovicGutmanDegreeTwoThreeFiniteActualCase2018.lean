/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2018 : Family 10 := level10.get ⟨1664,by decide⟩
def sourceMap2018 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2018 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2018_checked : acceptsGraphIso
    (source (graph core2018) (root 10) 0 2) DegreeTwoThreeSpectrum3807.graph sourceMap2018=true := by decide +kernel
theorem fusedMap2018_checked : acceptsGraphIso
    (fused (graph core2018) (root 10) 0 2) DegreeTwoThreeSpectrum3236.graph fusedMap2018=true := by decide +kernel
theorem certified2018 : Certified (graph core2018) (root 10) 0 2 :=
  of_native_maps core2018 DegreeTwoThreeSpectrum3807.graph DegreeTwoThreeSpectrum3236.graph
    sourceMap2018 fusedMap2018 sourceMap2018_checked fusedMap2018_checked
    DegreeTwoThreeFiniteComparisons.comparison2018
#print axioms sourceMap2018_checked
#print axioms fusedMap2018_checked
#print axioms certified2018
def sourceMap2018swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2018swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2018swap_checked : acceptsGraphIso
    (source (graph core2018) (root 10) 2 0) DegreeTwoThreeSpectrum3807.graph sourceMap2018swap=true := by decide +kernel
theorem fusedMap2018swap_checked : acceptsGraphIso
    (fused (graph core2018) (root 10) 2 0) DegreeTwoThreeSpectrum3236.graph fusedMap2018swap=true := by decide +kernel
theorem certified2018swap : Certified (graph core2018) (root 10) 2 0 :=
  of_native_maps core2018 DegreeTwoThreeSpectrum3807.graph DegreeTwoThreeSpectrum3236.graph
    sourceMap2018swap fusedMap2018swap sourceMap2018swap_checked fusedMap2018swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2018
#print axioms sourceMap2018swap_checked
#print axioms fusedMap2018swap_checked
#print axioms certified2018swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
