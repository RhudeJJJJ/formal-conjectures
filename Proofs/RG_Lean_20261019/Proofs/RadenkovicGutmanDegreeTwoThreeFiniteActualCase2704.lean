/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2704 : Family 10 := level10.get ⟨825,by decide⟩
def sourceMap2704 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2704 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2704_checked : acceptsGraphIso
    (source (graph core2704) (root 10) 0 4) DegreeTwoThreeSpectrum6794.graph sourceMap2704=true := by decide +kernel
theorem fusedMap2704_checked : acceptsGraphIso
    (fused (graph core2704) (root 10) 0 4) DegreeTwoThreeSpectrum5635.graph fusedMap2704=true := by decide +kernel
theorem certified2704 : Certified (graph core2704) (root 10) 0 4 :=
  of_native_maps core2704 DegreeTwoThreeSpectrum6794.graph DegreeTwoThreeSpectrum5635.graph
    sourceMap2704 fusedMap2704 sourceMap2704_checked fusedMap2704_checked
    DegreeTwoThreeFiniteComparisons.comparison2704
#print axioms sourceMap2704_checked
#print axioms fusedMap2704_checked
#print axioms certified2704
def sourceMap2704swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2704swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2704swap_checked : acceptsGraphIso
    (source (graph core2704) (root 10) 4 0) DegreeTwoThreeSpectrum6794.graph sourceMap2704swap=true := by decide +kernel
theorem fusedMap2704swap_checked : acceptsGraphIso
    (fused (graph core2704) (root 10) 4 0) DegreeTwoThreeSpectrum5635.graph fusedMap2704swap=true := by decide +kernel
theorem certified2704swap : Certified (graph core2704) (root 10) 4 0 :=
  of_native_maps core2704 DegreeTwoThreeSpectrum6794.graph DegreeTwoThreeSpectrum5635.graph
    sourceMap2704swap fusedMap2704swap sourceMap2704swap_checked fusedMap2704swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2704
#print axioms sourceMap2704swap_checked
#print axioms fusedMap2704swap_checked
#print axioms certified2704swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
