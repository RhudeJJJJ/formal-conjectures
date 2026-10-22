/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2572 : Family 10 := level10.get ⟨452,by decide⟩
def sourceMap2572 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2572 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2572_checked : acceptsGraphIso
    (source (graph core2572) (root 10) 0 4) DegreeTwoThreeSpectrum5879.graph sourceMap2572=true := by decide +kernel
theorem fusedMap2572_checked : acceptsGraphIso
    (fused (graph core2572) (root 10) 0 4) DegreeTwoThreeSpectrum5880.graph fusedMap2572=true := by decide +kernel
theorem certified2572 : Certified (graph core2572) (root 10) 0 4 :=
  of_native_maps core2572 DegreeTwoThreeSpectrum5879.graph DegreeTwoThreeSpectrum5880.graph
    sourceMap2572 fusedMap2572 sourceMap2572_checked fusedMap2572_checked
    DegreeTwoThreeFiniteComparisons.comparison2572
#print axioms sourceMap2572_checked
#print axioms fusedMap2572_checked
#print axioms certified2572
def sourceMap2572swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2572swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2572swap_checked : acceptsGraphIso
    (source (graph core2572) (root 10) 4 0) DegreeTwoThreeSpectrum5879.graph sourceMap2572swap=true := by decide +kernel
theorem fusedMap2572swap_checked : acceptsGraphIso
    (fused (graph core2572) (root 10) 4 0) DegreeTwoThreeSpectrum5880.graph fusedMap2572swap=true := by decide +kernel
theorem certified2572swap : Certified (graph core2572) (root 10) 4 0 :=
  of_native_maps core2572 DegreeTwoThreeSpectrum5879.graph DegreeTwoThreeSpectrum5880.graph
    sourceMap2572swap fusedMap2572swap sourceMap2572swap_checked fusedMap2572swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2572
#print axioms sourceMap2572swap_checked
#print axioms fusedMap2572swap_checked
#print axioms certified2572swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
