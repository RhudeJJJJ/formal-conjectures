/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2673 : Family 10 := level10.get ⟨748,by decide⟩
def sourceMap2673 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2673 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2673_checked : acceptsGraphIso
    (source (graph core2673) (root 10) 0 4) DegreeTwoThreeSpectrum6650.graph sourceMap2673=true := by decide +kernel
theorem fusedMap2673_checked : acceptsGraphIso
    (fused (graph core2673) (root 10) 0 4) DegreeTwoThreeSpectrum5510.graph fusedMap2673=true := by decide +kernel
theorem certified2673 : Certified (graph core2673) (root 10) 0 4 :=
  of_native_maps core2673 DegreeTwoThreeSpectrum6650.graph DegreeTwoThreeSpectrum5510.graph
    sourceMap2673 fusedMap2673 sourceMap2673_checked fusedMap2673_checked
    DegreeTwoThreeFiniteComparisons.comparison2673
#print axioms sourceMap2673_checked
#print axioms fusedMap2673_checked
#print axioms certified2673
def sourceMap2673swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2673swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2673swap_checked : acceptsGraphIso
    (source (graph core2673) (root 10) 4 0) DegreeTwoThreeSpectrum6650.graph sourceMap2673swap=true := by decide +kernel
theorem fusedMap2673swap_checked : acceptsGraphIso
    (fused (graph core2673) (root 10) 4 0) DegreeTwoThreeSpectrum5510.graph fusedMap2673swap=true := by decide +kernel
theorem certified2673swap : Certified (graph core2673) (root 10) 4 0 :=
  of_native_maps core2673 DegreeTwoThreeSpectrum6650.graph DegreeTwoThreeSpectrum5510.graph
    sourceMap2673swap fusedMap2673swap sourceMap2673swap_checked fusedMap2673swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2673
#print axioms sourceMap2673swap_checked
#print axioms fusedMap2673swap_checked
#print axioms certified2673swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
