/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2630 : Family 10 := level10.get ⟨627,by decide⟩
def sourceMap2630 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2630 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2630_checked : acceptsGraphIso
    (source (graph core2630) (root 10) 0 4) DegreeTwoThreeSpectrum6375.graph sourceMap2630=true := by decide +kernel
theorem fusedMap2630_checked : acceptsGraphIso
    (fused (graph core2630) (root 10) 0 4) DegreeTwoThreeSpectrum5317.graph fusedMap2630=true := by decide +kernel
theorem certified2630 : Certified (graph core2630) (root 10) 0 4 :=
  of_native_maps core2630 DegreeTwoThreeSpectrum6375.graph DegreeTwoThreeSpectrum5317.graph
    sourceMap2630 fusedMap2630 sourceMap2630_checked fusedMap2630_checked
    DegreeTwoThreeFiniteComparisons.comparison2630
#print axioms sourceMap2630_checked
#print axioms fusedMap2630_checked
#print axioms certified2630
def sourceMap2630swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2630swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2630swap_checked : acceptsGraphIso
    (source (graph core2630) (root 10) 4 0) DegreeTwoThreeSpectrum6375.graph sourceMap2630swap=true := by decide +kernel
theorem fusedMap2630swap_checked : acceptsGraphIso
    (fused (graph core2630) (root 10) 4 0) DegreeTwoThreeSpectrum5317.graph fusedMap2630swap=true := by decide +kernel
theorem certified2630swap : Certified (graph core2630) (root 10) 4 0 :=
  of_native_maps core2630 DegreeTwoThreeSpectrum6375.graph DegreeTwoThreeSpectrum5317.graph
    sourceMap2630swap fusedMap2630swap sourceMap2630swap_checked fusedMap2630swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2630
#print axioms sourceMap2630swap_checked
#print axioms fusedMap2630swap_checked
#print axioms certified2630swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
