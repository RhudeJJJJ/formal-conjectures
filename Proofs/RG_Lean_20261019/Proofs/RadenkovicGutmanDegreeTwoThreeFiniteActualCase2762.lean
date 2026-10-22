/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2762 : Family 10 := level10.get ⟨975,by decide⟩
def sourceMap2762 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,16,11,12,13,14,15] (sourceLabel 10 0 4 v)
def fusedMap2762 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2762_checked : acceptsGraphIso
    (source (graph core2762) (root 10) 0 4) DegreeTwoThreeSpectrum7041.graph sourceMap2762=true := by decide +kernel
theorem fusedMap2762_checked : acceptsGraphIso
    (fused (graph core2762) (root 10) 0 4) DegreeTwoThreeSpectrum5909.graph fusedMap2762=true := by decide +kernel
theorem certified2762 : Certified (graph core2762) (root 10) 0 4 :=
  of_native_maps core2762 DegreeTwoThreeSpectrum7041.graph DegreeTwoThreeSpectrum5909.graph
    sourceMap2762 fusedMap2762 sourceMap2762_checked fusedMap2762_checked
    DegreeTwoThreeFiniteComparisons.comparison2762
#print axioms sourceMap2762_checked
#print axioms fusedMap2762_checked
#print axioms certified2762
def sourceMap2762swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 4 0 v)
def fusedMap2762swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2762swap_checked : acceptsGraphIso
    (source (graph core2762) (root 10) 4 0) DegreeTwoThreeSpectrum7041.graph sourceMap2762swap=true := by decide +kernel
theorem fusedMap2762swap_checked : acceptsGraphIso
    (fused (graph core2762) (root 10) 4 0) DegreeTwoThreeSpectrum5909.graph fusedMap2762swap=true := by decide +kernel
theorem certified2762swap : Certified (graph core2762) (root 10) 4 0 :=
  of_native_maps core2762 DegreeTwoThreeSpectrum7041.graph DegreeTwoThreeSpectrum5909.graph
    sourceMap2762swap fusedMap2762swap sourceMap2762swap_checked fusedMap2762swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2762
#print axioms sourceMap2762swap_checked
#print axioms fusedMap2762swap_checked
#print axioms certified2762swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
