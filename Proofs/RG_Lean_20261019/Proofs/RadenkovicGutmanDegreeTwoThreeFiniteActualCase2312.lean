/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2312 : Family 9 := level9.get ⟨327,by decide⟩
def sourceMap2312 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2312 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2312_checked : acceptsGraphIso
    (source (graph core2312) (root 9) 0 4) DegreeTwoThreeSpectrum4198.graph sourceMap2312=true := by decide +kernel
theorem fusedMap2312_checked : acceptsGraphIso
    (fused (graph core2312) (root 9) 0 4) DegreeTwoThreeSpectrum4199.graph fusedMap2312=true := by decide +kernel
theorem certified2312 : Certified (graph core2312) (root 9) 0 4 :=
  of_native_maps core2312 DegreeTwoThreeSpectrum4198.graph DegreeTwoThreeSpectrum4199.graph
    sourceMap2312 fusedMap2312 sourceMap2312_checked fusedMap2312_checked
    DegreeTwoThreeFiniteComparisons.comparison2312
#print axioms sourceMap2312_checked
#print axioms fusedMap2312_checked
#print axioms certified2312
def sourceMap2312swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2312swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2312swap_checked : acceptsGraphIso
    (source (graph core2312) (root 9) 4 0) DegreeTwoThreeSpectrum4198.graph sourceMap2312swap=true := by decide +kernel
theorem fusedMap2312swap_checked : acceptsGraphIso
    (fused (graph core2312) (root 9) 4 0) DegreeTwoThreeSpectrum4199.graph fusedMap2312swap=true := by decide +kernel
theorem certified2312swap : Certified (graph core2312) (root 9) 4 0 :=
  of_native_maps core2312 DegreeTwoThreeSpectrum4198.graph DegreeTwoThreeSpectrum4199.graph
    sourceMap2312swap fusedMap2312swap sourceMap2312swap_checked fusedMap2312swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2312
#print axioms sourceMap2312swap_checked
#print axioms fusedMap2312swap_checked
#print axioms certified2312swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
