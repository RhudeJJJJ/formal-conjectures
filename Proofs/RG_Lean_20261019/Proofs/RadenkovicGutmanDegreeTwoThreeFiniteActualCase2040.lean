/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2040 : Family 10 := level10.get ⟨1740,by decide⟩
def sourceMap2040 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2040 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2040_checked : acceptsGraphIso
    (source (graph core2040) (root 10) 0 2) DegreeTwoThreeSpectrum3837.graph sourceMap2040=true := by decide +kernel
theorem fusedMap2040_checked : acceptsGraphIso
    (fused (graph core2040) (root 10) 0 2) DegreeTwoThreeSpectrum3463.graph fusedMap2040=true := by decide +kernel
theorem certified2040 : Certified (graph core2040) (root 10) 0 2 :=
  of_native_maps core2040 DegreeTwoThreeSpectrum3837.graph DegreeTwoThreeSpectrum3463.graph
    sourceMap2040 fusedMap2040 sourceMap2040_checked fusedMap2040_checked
    DegreeTwoThreeFiniteComparisons.comparison2040
#print axioms sourceMap2040_checked
#print axioms fusedMap2040_checked
#print axioms certified2040
def sourceMap2040swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2040swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2040swap_checked : acceptsGraphIso
    (source (graph core2040) (root 10) 2 0) DegreeTwoThreeSpectrum3837.graph sourceMap2040swap=true := by decide +kernel
theorem fusedMap2040swap_checked : acceptsGraphIso
    (fused (graph core2040) (root 10) 2 0) DegreeTwoThreeSpectrum3463.graph fusedMap2040swap=true := by decide +kernel
theorem certified2040swap : Certified (graph core2040) (root 10) 2 0 :=
  of_native_maps core2040 DegreeTwoThreeSpectrum3837.graph DegreeTwoThreeSpectrum3463.graph
    sourceMap2040swap fusedMap2040swap sourceMap2040swap_checked fusedMap2040swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2040
#print axioms sourceMap2040swap_checked
#print axioms fusedMap2040swap_checked
#print axioms certified2040swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
