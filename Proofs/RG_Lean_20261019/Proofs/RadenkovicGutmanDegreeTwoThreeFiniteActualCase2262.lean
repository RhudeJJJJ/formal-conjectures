/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2262 : Family 9 := level9.get ⟨185,by decide⟩
def sourceMap2262 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2262 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2262_checked : acceptsGraphIso
    (source (graph core2262) (root 9) 0 4) DegreeTwoThreeSpectrum4367.graph sourceMap2262=true := by decide +kernel
theorem fusedMap2262_checked : acceptsGraphIso
    (fused (graph core2262) (root 9) 0 4) DegreeTwoThreeSpectrum3954.graph fusedMap2262=true := by decide +kernel
theorem certified2262 : Certified (graph core2262) (root 9) 0 4 :=
  of_native_maps core2262 DegreeTwoThreeSpectrum4367.graph DegreeTwoThreeSpectrum3954.graph
    sourceMap2262 fusedMap2262 sourceMap2262_checked fusedMap2262_checked
    DegreeTwoThreeFiniteComparisons.comparison2262
#print axioms sourceMap2262_checked
#print axioms fusedMap2262_checked
#print axioms certified2262
def sourceMap2262swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2262swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2262swap_checked : acceptsGraphIso
    (source (graph core2262) (root 9) 4 0) DegreeTwoThreeSpectrum4367.graph sourceMap2262swap=true := by decide +kernel
theorem fusedMap2262swap_checked : acceptsGraphIso
    (fused (graph core2262) (root 9) 4 0) DegreeTwoThreeSpectrum3954.graph fusedMap2262swap=true := by decide +kernel
theorem certified2262swap : Certified (graph core2262) (root 9) 4 0 :=
  of_native_maps core2262 DegreeTwoThreeSpectrum4367.graph DegreeTwoThreeSpectrum3954.graph
    sourceMap2262swap fusedMap2262swap sourceMap2262swap_checked fusedMap2262swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2262
#print axioms sourceMap2262swap_checked
#print axioms fusedMap2262swap_checked
#print axioms certified2262swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
