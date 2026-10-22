/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2781 : Family 10 := level10.get ⟨1026,by decide⟩
def sourceMap2781 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2781 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2781_checked : acceptsGraphIso
    (source (graph core2781) (root 10) 0 4) DegreeTwoThreeSpectrum6033.graph sourceMap2781=true := by decide +kernel
theorem fusedMap2781_checked : acceptsGraphIso
    (fused (graph core2781) (root 10) 0 4) DegreeTwoThreeSpectrum6034.graph fusedMap2781=true := by decide +kernel
theorem certified2781 : Certified (graph core2781) (root 10) 0 4 :=
  of_native_maps core2781 DegreeTwoThreeSpectrum6033.graph DegreeTwoThreeSpectrum6034.graph
    sourceMap2781 fusedMap2781 sourceMap2781_checked fusedMap2781_checked
    DegreeTwoThreeFiniteComparisons.comparison2781
#print axioms sourceMap2781_checked
#print axioms fusedMap2781_checked
#print axioms certified2781
def sourceMap2781swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2781swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2781swap_checked : acceptsGraphIso
    (source (graph core2781) (root 10) 4 0) DegreeTwoThreeSpectrum6033.graph sourceMap2781swap=true := by decide +kernel
theorem fusedMap2781swap_checked : acceptsGraphIso
    (fused (graph core2781) (root 10) 4 0) DegreeTwoThreeSpectrum6034.graph fusedMap2781swap=true := by decide +kernel
theorem certified2781swap : Certified (graph core2781) (root 10) 4 0 :=
  of_native_maps core2781 DegreeTwoThreeSpectrum6033.graph DegreeTwoThreeSpectrum6034.graph
    sourceMap2781swap fusedMap2781swap sourceMap2781swap_checked fusedMap2781swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2781
#print axioms sourceMap2781swap_checked
#print axioms fusedMap2781swap_checked
#print axioms certified2781swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
