/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2908 : Family 10 := level10.get ⟨1337,by decide⟩
def sourceMap2908 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2908 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2908_checked : acceptsGraphIso
    (source (graph core2908) (root 10) 0 4) DegreeTwoThreeSpectrum6655.graph sourceMap2908=true := by decide +kernel
theorem fusedMap2908_checked : acceptsGraphIso
    (fused (graph core2908) (root 10) 0 4) DegreeTwoThreeSpectrum6656.graph fusedMap2908=true := by decide +kernel
theorem certified2908 : Certified (graph core2908) (root 10) 0 4 :=
  of_native_maps core2908 DegreeTwoThreeSpectrum6655.graph DegreeTwoThreeSpectrum6656.graph
    sourceMap2908 fusedMap2908 sourceMap2908_checked fusedMap2908_checked
    DegreeTwoThreeFiniteComparisons.comparison2908
#print axioms sourceMap2908_checked
#print axioms fusedMap2908_checked
#print axioms certified2908
def sourceMap2908swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2908swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2908swap_checked : acceptsGraphIso
    (source (graph core2908) (root 10) 4 0) DegreeTwoThreeSpectrum6655.graph sourceMap2908swap=true := by decide +kernel
theorem fusedMap2908swap_checked : acceptsGraphIso
    (fused (graph core2908) (root 10) 4 0) DegreeTwoThreeSpectrum6656.graph fusedMap2908swap=true := by decide +kernel
theorem certified2908swap : Certified (graph core2908) (root 10) 4 0 :=
  of_native_maps core2908 DegreeTwoThreeSpectrum6655.graph DegreeTwoThreeSpectrum6656.graph
    sourceMap2908swap fusedMap2908swap sourceMap2908swap_checked fusedMap2908swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2908
#print axioms sourceMap2908swap_checked
#print axioms fusedMap2908swap_checked
#print axioms certified2908swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
