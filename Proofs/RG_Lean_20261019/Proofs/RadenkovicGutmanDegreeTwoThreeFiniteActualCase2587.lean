/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2587 : Family 10 := level10.get ⟨488,by decide⟩
def sourceMap2587 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,10,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2587 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 0 4 v)
theorem sourceMap2587_checked : acceptsGraphIso
    (source (graph core2587) (root 10) 0 4) DegreeTwoThreeSpectrum5913.graph sourceMap2587=true := by decide +kernel
theorem fusedMap2587_checked : acceptsGraphIso
    (fused (graph core2587) (root 10) 0 4) DegreeTwoThreeSpectrum5953.graph fusedMap2587=true := by decide +kernel
theorem certified2587 : Certified (graph core2587) (root 10) 0 4 :=
  of_native_maps core2587 DegreeTwoThreeSpectrum5913.graph DegreeTwoThreeSpectrum5953.graph
    sourceMap2587 fusedMap2587 sourceMap2587_checked fusedMap2587_checked
    DegreeTwoThreeFiniteComparisons.comparison2587
#print axioms sourceMap2587_checked
#print axioms fusedMap2587_checked
#print axioms certified2587
def sourceMap2587swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,1,2,3,4,5,10] (sourceLabel 10 4 0 v)
def fusedMap2587swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 4 0 v)
theorem sourceMap2587swap_checked : acceptsGraphIso
    (source (graph core2587) (root 10) 4 0) DegreeTwoThreeSpectrum5913.graph sourceMap2587swap=true := by decide +kernel
theorem fusedMap2587swap_checked : acceptsGraphIso
    (fused (graph core2587) (root 10) 4 0) DegreeTwoThreeSpectrum5953.graph fusedMap2587swap=true := by decide +kernel
theorem certified2587swap : Certified (graph core2587) (root 10) 4 0 :=
  of_native_maps core2587 DegreeTwoThreeSpectrum5913.graph DegreeTwoThreeSpectrum5953.graph
    sourceMap2587swap fusedMap2587swap sourceMap2587swap_checked fusedMap2587swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2587
#print axioms sourceMap2587swap_checked
#print axioms fusedMap2587swap_checked
#print axioms certified2587swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
