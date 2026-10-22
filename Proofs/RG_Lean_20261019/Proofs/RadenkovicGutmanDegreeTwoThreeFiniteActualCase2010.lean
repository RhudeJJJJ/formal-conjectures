/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2010 : Family 10 := level10.get ⟨1647,by decide⟩
def sourceMap2010 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2010 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2010_checked : acceptsGraphIso
    (source (graph core2010) (root 10) 0 2) DegreeTwoThreeSpectrum3798.graph sourceMap2010=true := by decide +kernel
theorem fusedMap2010_checked : acceptsGraphIso
    (fused (graph core2010) (root 10) 0 2) DegreeTwoThreeSpectrum3205.graph fusedMap2010=true := by decide +kernel
theorem certified2010 : Certified (graph core2010) (root 10) 0 2 :=
  of_native_maps core2010 DegreeTwoThreeSpectrum3798.graph DegreeTwoThreeSpectrum3205.graph
    sourceMap2010 fusedMap2010 sourceMap2010_checked fusedMap2010_checked
    DegreeTwoThreeFiniteComparisons.comparison2010
#print axioms sourceMap2010_checked
#print axioms fusedMap2010_checked
#print axioms certified2010
def sourceMap2010swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2010swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2010swap_checked : acceptsGraphIso
    (source (graph core2010) (root 10) 2 0) DegreeTwoThreeSpectrum3798.graph sourceMap2010swap=true := by decide +kernel
theorem fusedMap2010swap_checked : acceptsGraphIso
    (fused (graph core2010) (root 10) 2 0) DegreeTwoThreeSpectrum3205.graph fusedMap2010swap=true := by decide +kernel
theorem certified2010swap : Certified (graph core2010) (root 10) 2 0 :=
  of_native_maps core2010 DegreeTwoThreeSpectrum3798.graph DegreeTwoThreeSpectrum3205.graph
    sourceMap2010swap fusedMap2010swap sourceMap2010swap_checked fusedMap2010swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2010
#print axioms sourceMap2010swap_checked
#print axioms fusedMap2010swap_checked
#print axioms certified2010swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
