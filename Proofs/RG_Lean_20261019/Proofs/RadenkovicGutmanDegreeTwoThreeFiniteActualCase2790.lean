/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2790 : Family 10 := level10.get ⟨1051,by decide⟩
def sourceMap2790 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2790 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2790_checked : acceptsGraphIso
    (source (graph core2790) (root 10) 0 4) DegreeTwoThreeSpectrum6086.graph sourceMap2790=true := by decide +kernel
theorem fusedMap2790_checked : acceptsGraphIso
    (fused (graph core2790) (root 10) 0 4) DegreeTwoThreeSpectrum6087.graph fusedMap2790=true := by decide +kernel
theorem certified2790 : Certified (graph core2790) (root 10) 0 4 :=
  of_native_maps core2790 DegreeTwoThreeSpectrum6086.graph DegreeTwoThreeSpectrum6087.graph
    sourceMap2790 fusedMap2790 sourceMap2790_checked fusedMap2790_checked
    DegreeTwoThreeFiniteComparisons.comparison2790
#print axioms sourceMap2790_checked
#print axioms fusedMap2790_checked
#print axioms certified2790
def sourceMap2790swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2790swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2790swap_checked : acceptsGraphIso
    (source (graph core2790) (root 10) 4 0) DegreeTwoThreeSpectrum6086.graph sourceMap2790swap=true := by decide +kernel
theorem fusedMap2790swap_checked : acceptsGraphIso
    (fused (graph core2790) (root 10) 4 0) DegreeTwoThreeSpectrum6087.graph fusedMap2790swap=true := by decide +kernel
theorem certified2790swap : Certified (graph core2790) (root 10) 4 0 :=
  of_native_maps core2790 DegreeTwoThreeSpectrum6086.graph DegreeTwoThreeSpectrum6087.graph
    sourceMap2790swap fusedMap2790swap sourceMap2790swap_checked fusedMap2790swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2790
#print axioms sourceMap2790swap_checked
#print axioms fusedMap2790swap_checked
#print axioms certified2790swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
