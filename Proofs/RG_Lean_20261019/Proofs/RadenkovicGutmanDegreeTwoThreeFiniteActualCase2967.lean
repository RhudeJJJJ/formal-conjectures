/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2967 : Family 10 := level10.get ⟨1470,by decide⟩
def sourceMap2967 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2967 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2967_checked : acceptsGraphIso
    (source (graph core2967) (root 10) 0 4) DegreeTwoThreeSpectrum6952.graph sourceMap2967=true := by decide +kernel
theorem fusedMap2967_checked : acceptsGraphIso
    (fused (graph core2967) (root 10) 0 4) DegreeTwoThreeSpectrum6953.graph fusedMap2967=true := by decide +kernel
theorem certified2967 : Certified (graph core2967) (root 10) 0 4 :=
  of_native_maps core2967 DegreeTwoThreeSpectrum6952.graph DegreeTwoThreeSpectrum6953.graph
    sourceMap2967 fusedMap2967 sourceMap2967_checked fusedMap2967_checked
    DegreeTwoThreeFiniteComparisons.comparison2967
#print axioms sourceMap2967_checked
#print axioms fusedMap2967_checked
#print axioms certified2967
def sourceMap2967swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2967swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2967swap_checked : acceptsGraphIso
    (source (graph core2967) (root 10) 4 0) DegreeTwoThreeSpectrum6952.graph sourceMap2967swap=true := by decide +kernel
theorem fusedMap2967swap_checked : acceptsGraphIso
    (fused (graph core2967) (root 10) 4 0) DegreeTwoThreeSpectrum6953.graph fusedMap2967swap=true := by decide +kernel
theorem certified2967swap : Certified (graph core2967) (root 10) 4 0 :=
  of_native_maps core2967 DegreeTwoThreeSpectrum6952.graph DegreeTwoThreeSpectrum6953.graph
    sourceMap2967swap fusedMap2967swap sourceMap2967swap_checked fusedMap2967swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2967
#print axioms sourceMap2967swap_checked
#print axioms fusedMap2967swap_checked
#print axioms certified2967swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
