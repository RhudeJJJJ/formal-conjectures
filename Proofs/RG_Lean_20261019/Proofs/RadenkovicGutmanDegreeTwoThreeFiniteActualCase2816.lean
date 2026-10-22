/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2816 : Family 10 := level10.get ⟨1119,by decide⟩
def sourceMap2816 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2816 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2816_checked : acceptsGraphIso
    (source (graph core2816) (root 10) 0 4) DegreeTwoThreeSpectrum6223.graph sourceMap2816=true := by decide +kernel
theorem fusedMap2816_checked : acceptsGraphIso
    (fused (graph core2816) (root 10) 0 4) DegreeTwoThreeSpectrum6224.graph fusedMap2816=true := by decide +kernel
theorem certified2816 : Certified (graph core2816) (root 10) 0 4 :=
  of_native_maps core2816 DegreeTwoThreeSpectrum6223.graph DegreeTwoThreeSpectrum6224.graph
    sourceMap2816 fusedMap2816 sourceMap2816_checked fusedMap2816_checked
    DegreeTwoThreeFiniteComparisons.comparison2816
#print axioms sourceMap2816_checked
#print axioms fusedMap2816_checked
#print axioms certified2816
def sourceMap2816swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2816swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2816swap_checked : acceptsGraphIso
    (source (graph core2816) (root 10) 4 0) DegreeTwoThreeSpectrum6223.graph sourceMap2816swap=true := by decide +kernel
theorem fusedMap2816swap_checked : acceptsGraphIso
    (fused (graph core2816) (root 10) 4 0) DegreeTwoThreeSpectrum6224.graph fusedMap2816swap=true := by decide +kernel
theorem certified2816swap : Certified (graph core2816) (root 10) 4 0 :=
  of_native_maps core2816 DegreeTwoThreeSpectrum6223.graph DegreeTwoThreeSpectrum6224.graph
    sourceMap2816swap fusedMap2816swap sourceMap2816swap_checked fusedMap2816swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2816
#print axioms sourceMap2816swap_checked
#print axioms fusedMap2816swap_checked
#print axioms certified2816swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
