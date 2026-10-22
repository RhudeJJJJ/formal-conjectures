/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2797 : Family 10 := level10.get ⟨1071,by decide⟩
def sourceMap2797 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2797 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2797_checked : acceptsGraphIso
    (source (graph core2797) (root 10) 0 4) DegreeTwoThreeSpectrum6130.graph sourceMap2797=true := by decide +kernel
theorem fusedMap2797_checked : acceptsGraphIso
    (fused (graph core2797) (root 10) 0 4) DegreeTwoThreeSpectrum6131.graph fusedMap2797=true := by decide +kernel
theorem certified2797 : Certified (graph core2797) (root 10) 0 4 :=
  of_native_maps core2797 DegreeTwoThreeSpectrum6130.graph DegreeTwoThreeSpectrum6131.graph
    sourceMap2797 fusedMap2797 sourceMap2797_checked fusedMap2797_checked
    DegreeTwoThreeFiniteComparisons.comparison2797
#print axioms sourceMap2797_checked
#print axioms fusedMap2797_checked
#print axioms certified2797
def sourceMap2797swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2797swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2797swap_checked : acceptsGraphIso
    (source (graph core2797) (root 10) 4 0) DegreeTwoThreeSpectrum6130.graph sourceMap2797swap=true := by decide +kernel
theorem fusedMap2797swap_checked : acceptsGraphIso
    (fused (graph core2797) (root 10) 4 0) DegreeTwoThreeSpectrum6131.graph fusedMap2797swap=true := by decide +kernel
theorem certified2797swap : Certified (graph core2797) (root 10) 4 0 :=
  of_native_maps core2797 DegreeTwoThreeSpectrum6130.graph DegreeTwoThreeSpectrum6131.graph
    sourceMap2797swap fusedMap2797swap sourceMap2797swap_checked fusedMap2797swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2797
#print axioms sourceMap2797swap_checked
#print axioms fusedMap2797swap_checked
#print axioms certified2797swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
