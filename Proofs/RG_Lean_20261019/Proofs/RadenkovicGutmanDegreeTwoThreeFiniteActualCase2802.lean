/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2802 : Family 10 := level10.get ⟨1081,by decide⟩
def sourceMap2802 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2802 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2802_checked : acceptsGraphIso
    (source (graph core2802) (root 10) 0 4) DegreeTwoThreeSpectrum6144.graph sourceMap2802=true := by decide +kernel
theorem fusedMap2802_checked : acceptsGraphIso
    (fused (graph core2802) (root 10) 0 4) DegreeTwoThreeSpectrum6145.graph fusedMap2802=true := by decide +kernel
theorem certified2802 : Certified (graph core2802) (root 10) 0 4 :=
  of_native_maps core2802 DegreeTwoThreeSpectrum6144.graph DegreeTwoThreeSpectrum6145.graph
    sourceMap2802 fusedMap2802 sourceMap2802_checked fusedMap2802_checked
    DegreeTwoThreeFiniteComparisons.comparison2802
#print axioms sourceMap2802_checked
#print axioms fusedMap2802_checked
#print axioms certified2802
def sourceMap2802swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2802swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2802swap_checked : acceptsGraphIso
    (source (graph core2802) (root 10) 4 0) DegreeTwoThreeSpectrum6144.graph sourceMap2802swap=true := by decide +kernel
theorem fusedMap2802swap_checked : acceptsGraphIso
    (fused (graph core2802) (root 10) 4 0) DegreeTwoThreeSpectrum6145.graph fusedMap2802swap=true := by decide +kernel
theorem certified2802swap : Certified (graph core2802) (root 10) 4 0 :=
  of_native_maps core2802 DegreeTwoThreeSpectrum6144.graph DegreeTwoThreeSpectrum6145.graph
    sourceMap2802swap fusedMap2802swap sourceMap2802swap_checked fusedMap2802swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2802
#print axioms sourceMap2802swap_checked
#print axioms fusedMap2802swap_checked
#print axioms certified2802swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
