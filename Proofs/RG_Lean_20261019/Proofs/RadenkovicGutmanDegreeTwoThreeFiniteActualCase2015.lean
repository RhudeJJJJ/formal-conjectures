/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2015 : Family 10 := level10.get ⟨1655,by decide⟩
def sourceMap2015 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2015 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2015_checked : acceptsGraphIso
    (source (graph core2015) (root 10) 0 2) DegreeTwoThreeSpectrum3803.graph sourceMap2015=true := by decide +kernel
theorem fusedMap2015_checked : acceptsGraphIso
    (fused (graph core2015) (root 10) 0 2) DegreeTwoThreeSpectrum3218.graph fusedMap2015=true := by decide +kernel
theorem certified2015 : Certified (graph core2015) (root 10) 0 2 :=
  of_native_maps core2015 DegreeTwoThreeSpectrum3803.graph DegreeTwoThreeSpectrum3218.graph
    sourceMap2015 fusedMap2015 sourceMap2015_checked fusedMap2015_checked
    DegreeTwoThreeFiniteComparisons.comparison2015
#print axioms sourceMap2015_checked
#print axioms fusedMap2015_checked
#print axioms certified2015
def sourceMap2015swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2015swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2015swap_checked : acceptsGraphIso
    (source (graph core2015) (root 10) 2 0) DegreeTwoThreeSpectrum3803.graph sourceMap2015swap=true := by decide +kernel
theorem fusedMap2015swap_checked : acceptsGraphIso
    (fused (graph core2015) (root 10) 2 0) DegreeTwoThreeSpectrum3218.graph fusedMap2015swap=true := by decide +kernel
theorem certified2015swap : Certified (graph core2015) (root 10) 2 0 :=
  of_native_maps core2015 DegreeTwoThreeSpectrum3803.graph DegreeTwoThreeSpectrum3218.graph
    sourceMap2015swap fusedMap2015swap sourceMap2015swap_checked fusedMap2015swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2015
#print axioms sourceMap2015swap_checked
#print axioms fusedMap2015swap_checked
#print axioms certified2015swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
