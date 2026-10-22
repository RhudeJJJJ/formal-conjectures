/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2748 : Family 10 := level10.get ⟨946,by decide⟩
def sourceMap2748 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2748 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2748_checked : acceptsGraphIso
    (source (graph core2748) (root 10) 0 4) DegreeTwoThreeSpectrum7026.graph sourceMap2748=true := by decide +kernel
theorem fusedMap2748_checked : acceptsGraphIso
    (fused (graph core2748) (root 10) 0 4) DegreeTwoThreeSpectrum5845.graph fusedMap2748=true := by decide +kernel
theorem certified2748 : Certified (graph core2748) (root 10) 0 4 :=
  of_native_maps core2748 DegreeTwoThreeSpectrum7026.graph DegreeTwoThreeSpectrum5845.graph
    sourceMap2748 fusedMap2748 sourceMap2748_checked fusedMap2748_checked
    DegreeTwoThreeFiniteComparisons.comparison2748
#print axioms sourceMap2748_checked
#print axioms fusedMap2748_checked
#print axioms certified2748
def sourceMap2748swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2748swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2748swap_checked : acceptsGraphIso
    (source (graph core2748) (root 10) 4 0) DegreeTwoThreeSpectrum7026.graph sourceMap2748swap=true := by decide +kernel
theorem fusedMap2748swap_checked : acceptsGraphIso
    (fused (graph core2748) (root 10) 4 0) DegreeTwoThreeSpectrum5845.graph fusedMap2748swap=true := by decide +kernel
theorem certified2748swap : Certified (graph core2748) (root 10) 4 0 :=
  of_native_maps core2748 DegreeTwoThreeSpectrum7026.graph DegreeTwoThreeSpectrum5845.graph
    sourceMap2748swap fusedMap2748swap sourceMap2748swap_checked fusedMap2748swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2748
#print axioms sourceMap2748swap_checked
#print axioms fusedMap2748swap_checked
#print axioms certified2748swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
