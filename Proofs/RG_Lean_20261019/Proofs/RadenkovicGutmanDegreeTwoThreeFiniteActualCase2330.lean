/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2330 : Family 9 := level9.get ⟨377,by decide⟩
def sourceMap2330 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2330 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2330_checked : acceptsGraphIso
    (source (graph core2330) (root 9) 0 4) DegreeTwoThreeSpectrum4312.graph sourceMap2330=true := by decide +kernel
theorem fusedMap2330_checked : acceptsGraphIso
    (fused (graph core2330) (root 9) 0 4) DegreeTwoThreeSpectrum4313.graph fusedMap2330=true := by decide +kernel
theorem certified2330 : Certified (graph core2330) (root 9) 0 4 :=
  of_native_maps core2330 DegreeTwoThreeSpectrum4312.graph DegreeTwoThreeSpectrum4313.graph
    sourceMap2330 fusedMap2330 sourceMap2330_checked fusedMap2330_checked
    DegreeTwoThreeFiniteComparisons.comparison2330
#print axioms sourceMap2330_checked
#print axioms fusedMap2330_checked
#print axioms certified2330
def sourceMap2330swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2330swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2330swap_checked : acceptsGraphIso
    (source (graph core2330) (root 9) 4 0) DegreeTwoThreeSpectrum4312.graph sourceMap2330swap=true := by decide +kernel
theorem fusedMap2330swap_checked : acceptsGraphIso
    (fused (graph core2330) (root 9) 4 0) DegreeTwoThreeSpectrum4313.graph fusedMap2330swap=true := by decide +kernel
theorem certified2330swap : Certified (graph core2330) (root 9) 4 0 :=
  of_native_maps core2330 DegreeTwoThreeSpectrum4312.graph DegreeTwoThreeSpectrum4313.graph
    sourceMap2330swap fusedMap2330swap sourceMap2330swap_checked fusedMap2330swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2330
#print axioms sourceMap2330swap_checked
#print axioms fusedMap2330swap_checked
#print axioms certified2330swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
