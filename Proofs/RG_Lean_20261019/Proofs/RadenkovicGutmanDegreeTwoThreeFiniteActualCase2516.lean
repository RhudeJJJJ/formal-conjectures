/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2516 : Family 10 := level10.get ⟨269,by decide⟩
def sourceMap2516 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2516 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2516_checked : acceptsGraphIso
    (source (graph core2516) (root 10) 0 4) DegreeTwoThreeSpectrum5390.graph sourceMap2516=true := by decide +kernel
theorem fusedMap2516_checked : acceptsGraphIso
    (fused (graph core2516) (root 10) 0 4) DegreeTwoThreeSpectrum5391.graph fusedMap2516=true := by decide +kernel
theorem certified2516 : Certified (graph core2516) (root 10) 0 4 :=
  of_native_maps core2516 DegreeTwoThreeSpectrum5390.graph DegreeTwoThreeSpectrum5391.graph
    sourceMap2516 fusedMap2516 sourceMap2516_checked fusedMap2516_checked
    DegreeTwoThreeFiniteComparisons.comparison2516
#print axioms sourceMap2516_checked
#print axioms fusedMap2516_checked
#print axioms certified2516
def sourceMap2516swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2516swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2516swap_checked : acceptsGraphIso
    (source (graph core2516) (root 10) 4 0) DegreeTwoThreeSpectrum5390.graph sourceMap2516swap=true := by decide +kernel
theorem fusedMap2516swap_checked : acceptsGraphIso
    (fused (graph core2516) (root 10) 4 0) DegreeTwoThreeSpectrum5391.graph fusedMap2516swap=true := by decide +kernel
theorem certified2516swap : Certified (graph core2516) (root 10) 4 0 :=
  of_native_maps core2516 DegreeTwoThreeSpectrum5390.graph DegreeTwoThreeSpectrum5391.graph
    sourceMap2516swap fusedMap2516swap sourceMap2516swap_checked fusedMap2516swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2516
#print axioms sourceMap2516swap_checked
#print axioms fusedMap2516swap_checked
#print axioms certified2516swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
