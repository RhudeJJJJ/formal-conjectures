/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2662 : Family 10 := level10.get ⟨716,by decide⟩
def sourceMap2662 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2662 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2662_checked : acceptsGraphIso
    (source (graph core2662) (root 10) 0 4) DegreeTwoThreeSpectrum6571.graph sourceMap2662=true := by decide +kernel
theorem fusedMap2662_checked : acceptsGraphIso
    (fused (graph core2662) (root 10) 0 4) DegreeTwoThreeSpectrum5462.graph fusedMap2662=true := by decide +kernel
theorem certified2662 : Certified (graph core2662) (root 10) 0 4 :=
  of_native_maps core2662 DegreeTwoThreeSpectrum6571.graph DegreeTwoThreeSpectrum5462.graph
    sourceMap2662 fusedMap2662 sourceMap2662_checked fusedMap2662_checked
    DegreeTwoThreeFiniteComparisons.comparison2662
#print axioms sourceMap2662_checked
#print axioms fusedMap2662_checked
#print axioms certified2662
def sourceMap2662swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2662swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2662swap_checked : acceptsGraphIso
    (source (graph core2662) (root 10) 4 0) DegreeTwoThreeSpectrum6571.graph sourceMap2662swap=true := by decide +kernel
theorem fusedMap2662swap_checked : acceptsGraphIso
    (fused (graph core2662) (root 10) 4 0) DegreeTwoThreeSpectrum5462.graph fusedMap2662swap=true := by decide +kernel
theorem certified2662swap : Certified (graph core2662) (root 10) 4 0 :=
  of_native_maps core2662 DegreeTwoThreeSpectrum6571.graph DegreeTwoThreeSpectrum5462.graph
    sourceMap2662swap fusedMap2662swap sourceMap2662swap_checked fusedMap2662swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2662
#print axioms sourceMap2662swap_checked
#print axioms fusedMap2662swap_checked
#print axioms certified2662swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
