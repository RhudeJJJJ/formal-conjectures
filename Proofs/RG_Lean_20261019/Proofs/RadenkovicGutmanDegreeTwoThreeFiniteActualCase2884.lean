/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2884 : Family 10 := level10.get ⟨1282,by decide⟩
def sourceMap2884 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2884 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2884_checked : acceptsGraphIso
    (source (graph core2884) (root 10) 0 4) DegreeTwoThreeSpectrum6548.graph sourceMap2884=true := by decide +kernel
theorem fusedMap2884_checked : acceptsGraphIso
    (fused (graph core2884) (root 10) 0 4) DegreeTwoThreeSpectrum6549.graph fusedMap2884=true := by decide +kernel
theorem certified2884 : Certified (graph core2884) (root 10) 0 4 :=
  of_native_maps core2884 DegreeTwoThreeSpectrum6548.graph DegreeTwoThreeSpectrum6549.graph
    sourceMap2884 fusedMap2884 sourceMap2884_checked fusedMap2884_checked
    DegreeTwoThreeFiniteComparisons.comparison2884
#print axioms sourceMap2884_checked
#print axioms fusedMap2884_checked
#print axioms certified2884
def sourceMap2884swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2884swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2884swap_checked : acceptsGraphIso
    (source (graph core2884) (root 10) 4 0) DegreeTwoThreeSpectrum6548.graph sourceMap2884swap=true := by decide +kernel
theorem fusedMap2884swap_checked : acceptsGraphIso
    (fused (graph core2884) (root 10) 4 0) DegreeTwoThreeSpectrum6549.graph fusedMap2884swap=true := by decide +kernel
theorem certified2884swap : Certified (graph core2884) (root 10) 4 0 :=
  of_native_maps core2884 DegreeTwoThreeSpectrum6548.graph DegreeTwoThreeSpectrum6549.graph
    sourceMap2884swap fusedMap2884swap sourceMap2884swap_checked fusedMap2884swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2884
#print axioms sourceMap2884swap_checked
#print axioms fusedMap2884swap_checked
#print axioms certified2884swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
