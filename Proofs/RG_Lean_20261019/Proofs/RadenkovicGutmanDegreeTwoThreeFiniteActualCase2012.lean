/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2012 : Family 10 := level10.get ⟨1650,by decide⟩
def sourceMap2012 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2012 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2012_checked : acceptsGraphIso
    (source (graph core2012) (root 10) 0 2) DegreeTwoThreeSpectrum3800.graph sourceMap2012=true := by decide +kernel
theorem fusedMap2012_checked : acceptsGraphIso
    (fused (graph core2012) (root 10) 0 2) DegreeTwoThreeSpectrum3209.graph fusedMap2012=true := by decide +kernel
theorem certified2012 : Certified (graph core2012) (root 10) 0 2 :=
  of_native_maps core2012 DegreeTwoThreeSpectrum3800.graph DegreeTwoThreeSpectrum3209.graph
    sourceMap2012 fusedMap2012 sourceMap2012_checked fusedMap2012_checked
    DegreeTwoThreeFiniteComparisons.comparison2012
#print axioms sourceMap2012_checked
#print axioms fusedMap2012_checked
#print axioms certified2012
def sourceMap2012swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2012swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2012swap_checked : acceptsGraphIso
    (source (graph core2012) (root 10) 2 0) DegreeTwoThreeSpectrum3800.graph sourceMap2012swap=true := by decide +kernel
theorem fusedMap2012swap_checked : acceptsGraphIso
    (fused (graph core2012) (root 10) 2 0) DegreeTwoThreeSpectrum3209.graph fusedMap2012swap=true := by decide +kernel
theorem certified2012swap : Certified (graph core2012) (root 10) 2 0 :=
  of_native_maps core2012 DegreeTwoThreeSpectrum3800.graph DegreeTwoThreeSpectrum3209.graph
    sourceMap2012swap fusedMap2012swap sourceMap2012swap_checked fusedMap2012swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2012
#print axioms sourceMap2012swap_checked
#print axioms fusedMap2012swap_checked
#print axioms certified2012swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
