/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2936 : Family 10 := level10.get ⟨1398,by decide⟩
def sourceMap2936 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2936 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2936_checked : acceptsGraphIso
    (source (graph core2936) (root 10) 0 4) DegreeTwoThreeSpectrum6766.graph sourceMap2936=true := by decide +kernel
theorem fusedMap2936_checked : acceptsGraphIso
    (fused (graph core2936) (root 10) 0 4) DegreeTwoThreeSpectrum6767.graph fusedMap2936=true := by decide +kernel
theorem certified2936 : Certified (graph core2936) (root 10) 0 4 :=
  of_native_maps core2936 DegreeTwoThreeSpectrum6766.graph DegreeTwoThreeSpectrum6767.graph
    sourceMap2936 fusedMap2936 sourceMap2936_checked fusedMap2936_checked
    DegreeTwoThreeFiniteComparisons.comparison2936
#print axioms sourceMap2936_checked
#print axioms fusedMap2936_checked
#print axioms certified2936
def sourceMap2936swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2936swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2936swap_checked : acceptsGraphIso
    (source (graph core2936) (root 10) 4 0) DegreeTwoThreeSpectrum6766.graph sourceMap2936swap=true := by decide +kernel
theorem fusedMap2936swap_checked : acceptsGraphIso
    (fused (graph core2936) (root 10) 4 0) DegreeTwoThreeSpectrum6767.graph fusedMap2936swap=true := by decide +kernel
theorem certified2936swap : Certified (graph core2936) (root 10) 4 0 :=
  of_native_maps core2936 DegreeTwoThreeSpectrum6766.graph DegreeTwoThreeSpectrum6767.graph
    sourceMap2936swap fusedMap2936swap sourceMap2936swap_checked fusedMap2936swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2936
#print axioms sourceMap2936swap_checked
#print axioms fusedMap2936swap_checked
#print axioms certified2936swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
