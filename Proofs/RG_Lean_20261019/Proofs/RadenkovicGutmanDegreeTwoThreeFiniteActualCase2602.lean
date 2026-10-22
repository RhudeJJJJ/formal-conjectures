/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2602 : Family 10 := level10.get ⟨541,by decide⟩
def sourceMap2602 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2602 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2602_checked : acceptsGraphIso
    (source (graph core2602) (root 10) 0 4) DegreeTwoThreeSpectrum6143.graph sourceMap2602=true := by decide +kernel
theorem fusedMap2602_checked : acceptsGraphIso
    (fused (graph core2602) (root 10) 0 4) DegreeTwoThreeSpectrum5190.graph fusedMap2602=true := by decide +kernel
theorem certified2602 : Certified (graph core2602) (root 10) 0 4 :=
  of_native_maps core2602 DegreeTwoThreeSpectrum6143.graph DegreeTwoThreeSpectrum5190.graph
    sourceMap2602 fusedMap2602 sourceMap2602_checked fusedMap2602_checked
    DegreeTwoThreeFiniteComparisons.comparison2602
#print axioms sourceMap2602_checked
#print axioms fusedMap2602_checked
#print axioms certified2602
def sourceMap2602swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2602swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2602swap_checked : acceptsGraphIso
    (source (graph core2602) (root 10) 4 0) DegreeTwoThreeSpectrum6143.graph sourceMap2602swap=true := by decide +kernel
theorem fusedMap2602swap_checked : acceptsGraphIso
    (fused (graph core2602) (root 10) 4 0) DegreeTwoThreeSpectrum5190.graph fusedMap2602swap=true := by decide +kernel
theorem certified2602swap : Certified (graph core2602) (root 10) 4 0 :=
  of_native_maps core2602 DegreeTwoThreeSpectrum6143.graph DegreeTwoThreeSpectrum5190.graph
    sourceMap2602swap fusedMap2602swap sourceMap2602swap_checked fusedMap2602swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2602
#print axioms sourceMap2602swap_checked
#print axioms fusedMap2602swap_checked
#print axioms certified2602swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
