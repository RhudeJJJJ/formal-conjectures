/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2555 : Family 10 := level10.get ⟨400,by decide⟩
def sourceMap2555 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2555 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2555_checked : acceptsGraphIso
    (source (graph core2555) (root 10) 0 4) DegreeTwoThreeSpectrum5754.graph sourceMap2555=true := by decide +kernel
theorem fusedMap2555_checked : acceptsGraphIso
    (fused (graph core2555) (root 10) 0 4) DegreeTwoThreeSpectrum5755.graph fusedMap2555=true := by decide +kernel
theorem certified2555 : Certified (graph core2555) (root 10) 0 4 :=
  of_native_maps core2555 DegreeTwoThreeSpectrum5754.graph DegreeTwoThreeSpectrum5755.graph
    sourceMap2555 fusedMap2555 sourceMap2555_checked fusedMap2555_checked
    DegreeTwoThreeFiniteComparisons.comparison2555
#print axioms sourceMap2555_checked
#print axioms fusedMap2555_checked
#print axioms certified2555
def sourceMap2555swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2555swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2555swap_checked : acceptsGraphIso
    (source (graph core2555) (root 10) 4 0) DegreeTwoThreeSpectrum5754.graph sourceMap2555swap=true := by decide +kernel
theorem fusedMap2555swap_checked : acceptsGraphIso
    (fused (graph core2555) (root 10) 4 0) DegreeTwoThreeSpectrum5755.graph fusedMap2555swap=true := by decide +kernel
theorem certified2555swap : Certified (graph core2555) (root 10) 4 0 :=
  of_native_maps core2555 DegreeTwoThreeSpectrum5754.graph DegreeTwoThreeSpectrum5755.graph
    sourceMap2555swap fusedMap2555swap sourceMap2555swap_checked fusedMap2555swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2555
#print axioms sourceMap2555swap_checked
#print axioms fusedMap2555swap_checked
#print axioms certified2555swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
