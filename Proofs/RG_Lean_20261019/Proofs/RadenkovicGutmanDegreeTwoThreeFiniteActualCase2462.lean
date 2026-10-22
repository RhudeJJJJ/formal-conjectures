/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2462 : Family 10 := level10.get ⟨51,by decide⟩
def sourceMap2462 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,7,8,9,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2462 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (fusedLabel 10 0 4 v)
theorem sourceMap2462_checked : acceptsGraphIso
    (source (graph core2462) (root 10) 0 4) DegreeTwoThreeSpectrum5108.graph sourceMap2462=true := by decide +kernel
theorem fusedMap2462_checked : acceptsGraphIso
    (fused (graph core2462) (root 10) 0 4) DegreeTwoThreeSpectrum5128.graph fusedMap2462=true := by decide +kernel
theorem certified2462 : Certified (graph core2462) (root 10) 0 4 :=
  of_native_maps core2462 DegreeTwoThreeSpectrum5108.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap2462 fusedMap2462 sourceMap2462_checked fusedMap2462_checked
    DegreeTwoThreeFiniteComparisons.comparison2462
#print axioms sourceMap2462_checked
#print axioms fusedMap2462_checked
#print axioms certified2462
def sourceMap2462swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,7,8,2,3,4,5,6,9] (sourceLabel 10 4 0 v)
def fusedMap2462swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (fusedLabel 10 4 0 v)
theorem sourceMap2462swap_checked : acceptsGraphIso
    (source (graph core2462) (root 10) 4 0) DegreeTwoThreeSpectrum5108.graph sourceMap2462swap=true := by decide +kernel
theorem fusedMap2462swap_checked : acceptsGraphIso
    (fused (graph core2462) (root 10) 4 0) DegreeTwoThreeSpectrum5128.graph fusedMap2462swap=true := by decide +kernel
theorem certified2462swap : Certified (graph core2462) (root 10) 4 0 :=
  of_native_maps core2462 DegreeTwoThreeSpectrum5108.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap2462swap fusedMap2462swap sourceMap2462swap_checked fusedMap2462swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2462
#print axioms sourceMap2462swap_checked
#print axioms fusedMap2462swap_checked
#print axioms certified2462swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
