/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2029 : Family 10 := level10.get ⟨1710,by decide⟩
def sourceMap2029 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2029 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2029_checked : acceptsGraphIso
    (source (graph core2029) (root 10) 0 2) DegreeTwoThreeSpectrum3823.graph sourceMap2029=true := by decide +kernel
theorem fusedMap2029_checked : acceptsGraphIso
    (fused (graph core2029) (root 10) 0 2) DegreeTwoThreeSpectrum3389.graph fusedMap2029=true := by decide +kernel
theorem certified2029 : Certified (graph core2029) (root 10) 0 2 :=
  of_native_maps core2029 DegreeTwoThreeSpectrum3823.graph DegreeTwoThreeSpectrum3389.graph
    sourceMap2029 fusedMap2029 sourceMap2029_checked fusedMap2029_checked
    DegreeTwoThreeFiniteComparisons.comparison2029
#print axioms sourceMap2029_checked
#print axioms fusedMap2029_checked
#print axioms certified2029
def sourceMap2029swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2029swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2029swap_checked : acceptsGraphIso
    (source (graph core2029) (root 10) 2 0) DegreeTwoThreeSpectrum3823.graph sourceMap2029swap=true := by decide +kernel
theorem fusedMap2029swap_checked : acceptsGraphIso
    (fused (graph core2029) (root 10) 2 0) DegreeTwoThreeSpectrum3389.graph fusedMap2029swap=true := by decide +kernel
theorem certified2029swap : Certified (graph core2029) (root 10) 2 0 :=
  of_native_maps core2029 DegreeTwoThreeSpectrum3823.graph DegreeTwoThreeSpectrum3389.graph
    sourceMap2029swap fusedMap2029swap sourceMap2029swap_checked fusedMap2029swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2029
#print axioms sourceMap2029swap_checked
#print axioms fusedMap2029swap_checked
#print axioms certified2029swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
