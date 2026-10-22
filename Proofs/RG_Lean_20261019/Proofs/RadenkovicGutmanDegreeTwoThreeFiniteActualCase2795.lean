/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2795 : Family 10 := level10.get ⟨1062,by decide⟩
def sourceMap2795 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2795 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2795_checked : acceptsGraphIso
    (source (graph core2795) (root 10) 0 4) DegreeTwoThreeSpectrum6108.graph sourceMap2795=true := by decide +kernel
theorem fusedMap2795_checked : acceptsGraphIso
    (fused (graph core2795) (root 10) 0 4) DegreeTwoThreeSpectrum6109.graph fusedMap2795=true := by decide +kernel
theorem certified2795 : Certified (graph core2795) (root 10) 0 4 :=
  of_native_maps core2795 DegreeTwoThreeSpectrum6108.graph DegreeTwoThreeSpectrum6109.graph
    sourceMap2795 fusedMap2795 sourceMap2795_checked fusedMap2795_checked
    DegreeTwoThreeFiniteComparisons.comparison2795
#print axioms sourceMap2795_checked
#print axioms fusedMap2795_checked
#print axioms certified2795
def sourceMap2795swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2795swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2795swap_checked : acceptsGraphIso
    (source (graph core2795) (root 10) 4 0) DegreeTwoThreeSpectrum6108.graph sourceMap2795swap=true := by decide +kernel
theorem fusedMap2795swap_checked : acceptsGraphIso
    (fused (graph core2795) (root 10) 4 0) DegreeTwoThreeSpectrum6109.graph fusedMap2795swap=true := by decide +kernel
theorem certified2795swap : Certified (graph core2795) (root 10) 4 0 :=
  of_native_maps core2795 DegreeTwoThreeSpectrum6108.graph DegreeTwoThreeSpectrum6109.graph
    sourceMap2795swap fusedMap2795swap sourceMap2795swap_checked fusedMap2795swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2795
#print axioms sourceMap2795swap_checked
#print axioms fusedMap2795swap_checked
#print axioms certified2795swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
