/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2595 : Family 10 := level10.get ⟨514,by decide⟩
def sourceMap2595 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2595 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2595_checked : acceptsGraphIso
    (source (graph core2595) (root 10) 0 4) DegreeTwoThreeSpectrum6044.graph sourceMap2595=true := by decide +kernel
theorem fusedMap2595_checked : acceptsGraphIso
    (fused (graph core2595) (root 10) 0 4) DegreeTwoThreeSpectrum5154.graph fusedMap2595=true := by decide +kernel
theorem certified2595 : Certified (graph core2595) (root 10) 0 4 :=
  of_native_maps core2595 DegreeTwoThreeSpectrum6044.graph DegreeTwoThreeSpectrum5154.graph
    sourceMap2595 fusedMap2595 sourceMap2595_checked fusedMap2595_checked
    DegreeTwoThreeFiniteComparisons.comparison2595
#print axioms sourceMap2595_checked
#print axioms fusedMap2595_checked
#print axioms certified2595
def sourceMap2595swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2595swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2595swap_checked : acceptsGraphIso
    (source (graph core2595) (root 10) 4 0) DegreeTwoThreeSpectrum6044.graph sourceMap2595swap=true := by decide +kernel
theorem fusedMap2595swap_checked : acceptsGraphIso
    (fused (graph core2595) (root 10) 4 0) DegreeTwoThreeSpectrum5154.graph fusedMap2595swap=true := by decide +kernel
theorem certified2595swap : Certified (graph core2595) (root 10) 4 0 :=
  of_native_maps core2595 DegreeTwoThreeSpectrum6044.graph DegreeTwoThreeSpectrum5154.graph
    sourceMap2595swap fusedMap2595swap sourceMap2595swap_checked fusedMap2595swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2595
#print axioms sourceMap2595swap_checked
#print axioms fusedMap2595swap_checked
#print axioms certified2595swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
