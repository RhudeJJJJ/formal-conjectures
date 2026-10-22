/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2504 : Family 10 := level10.get ⟨225,by decide⟩
def sourceMap2504 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2504 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2504_checked : acceptsGraphIso
    (source (graph core2504) (root 10) 0 4) DegreeTwoThreeSpectrum5262.graph sourceMap2504=true := by decide +kernel
theorem fusedMap2504_checked : acceptsGraphIso
    (fused (graph core2504) (root 10) 0 4) DegreeTwoThreeSpectrum5263.graph fusedMap2504=true := by decide +kernel
theorem certified2504 : Certified (graph core2504) (root 10) 0 4 :=
  of_native_maps core2504 DegreeTwoThreeSpectrum5262.graph DegreeTwoThreeSpectrum5263.graph
    sourceMap2504 fusedMap2504 sourceMap2504_checked fusedMap2504_checked
    DegreeTwoThreeFiniteComparisons.comparison2504
#print axioms sourceMap2504_checked
#print axioms fusedMap2504_checked
#print axioms certified2504
def sourceMap2504swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2504swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2504swap_checked : acceptsGraphIso
    (source (graph core2504) (root 10) 4 0) DegreeTwoThreeSpectrum5262.graph sourceMap2504swap=true := by decide +kernel
theorem fusedMap2504swap_checked : acceptsGraphIso
    (fused (graph core2504) (root 10) 4 0) DegreeTwoThreeSpectrum5263.graph fusedMap2504swap=true := by decide +kernel
theorem certified2504swap : Certified (graph core2504) (root 10) 4 0 :=
  of_native_maps core2504 DegreeTwoThreeSpectrum5262.graph DegreeTwoThreeSpectrum5263.graph
    sourceMap2504swap fusedMap2504swap sourceMap2504swap_checked fusedMap2504swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2504
#print axioms sourceMap2504swap_checked
#print axioms fusedMap2504swap_checked
#print axioms certified2504swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
