/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2716 : Family 10 := level10.get ⟨866,by decide⟩
def sourceMap2716 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2716 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2716_checked : acceptsGraphIso
    (source (graph core2716) (root 10) 0 4) DegreeTwoThreeSpectrum6926.graph sourceMap2716=true := by decide +kernel
theorem fusedMap2716_checked : acceptsGraphIso
    (fused (graph core2716) (root 10) 0 4) DegreeTwoThreeSpectrum5706.graph fusedMap2716=true := by decide +kernel
theorem certified2716 : Certified (graph core2716) (root 10) 0 4 :=
  of_native_maps core2716 DegreeTwoThreeSpectrum6926.graph DegreeTwoThreeSpectrum5706.graph
    sourceMap2716 fusedMap2716 sourceMap2716_checked fusedMap2716_checked
    DegreeTwoThreeFiniteComparisons.comparison2716
#print axioms sourceMap2716_checked
#print axioms fusedMap2716_checked
#print axioms certified2716
def sourceMap2716swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2716swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2716swap_checked : acceptsGraphIso
    (source (graph core2716) (root 10) 4 0) DegreeTwoThreeSpectrum6926.graph sourceMap2716swap=true := by decide +kernel
theorem fusedMap2716swap_checked : acceptsGraphIso
    (fused (graph core2716) (root 10) 4 0) DegreeTwoThreeSpectrum5706.graph fusedMap2716swap=true := by decide +kernel
theorem certified2716swap : Certified (graph core2716) (root 10) 4 0 :=
  of_native_maps core2716 DegreeTwoThreeSpectrum6926.graph DegreeTwoThreeSpectrum5706.graph
    sourceMap2716swap fusedMap2716swap sourceMap2716swap_checked fusedMap2716swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2716
#print axioms sourceMap2716swap_checked
#print axioms fusedMap2716swap_checked
#print axioms certified2716swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
