/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2810 : Family 10 := level10.get ⟨1101,by decide⟩
def sourceMap2810 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2810 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2810_checked : acceptsGraphIso
    (source (graph core2810) (root 10) 0 4) DegreeTwoThreeSpectrum6186.graph sourceMap2810=true := by decide +kernel
theorem fusedMap2810_checked : acceptsGraphIso
    (fused (graph core2810) (root 10) 0 4) DegreeTwoThreeSpectrum6187.graph fusedMap2810=true := by decide +kernel
theorem certified2810 : Certified (graph core2810) (root 10) 0 4 :=
  of_native_maps core2810 DegreeTwoThreeSpectrum6186.graph DegreeTwoThreeSpectrum6187.graph
    sourceMap2810 fusedMap2810 sourceMap2810_checked fusedMap2810_checked
    DegreeTwoThreeFiniteComparisons.comparison2810
#print axioms sourceMap2810_checked
#print axioms fusedMap2810_checked
#print axioms certified2810
def sourceMap2810swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2810swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2810swap_checked : acceptsGraphIso
    (source (graph core2810) (root 10) 4 0) DegreeTwoThreeSpectrum6186.graph sourceMap2810swap=true := by decide +kernel
theorem fusedMap2810swap_checked : acceptsGraphIso
    (fused (graph core2810) (root 10) 4 0) DegreeTwoThreeSpectrum6187.graph fusedMap2810swap=true := by decide +kernel
theorem certified2810swap : Certified (graph core2810) (root 10) 4 0 :=
  of_native_maps core2810 DegreeTwoThreeSpectrum6186.graph DegreeTwoThreeSpectrum6187.graph
    sourceMap2810swap fusedMap2810swap sourceMap2810swap_checked fusedMap2810swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2810
#print axioms sourceMap2810swap_checked
#print axioms fusedMap2810swap_checked
#print axioms certified2810swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
