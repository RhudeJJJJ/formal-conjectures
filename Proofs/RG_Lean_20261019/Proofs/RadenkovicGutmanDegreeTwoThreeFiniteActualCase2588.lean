/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2588 : Family 10 := level10.get ⟨489,by decide⟩
def sourceMap2588 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,10,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2588 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 0 4 v)
theorem sourceMap2588_checked : acceptsGraphIso
    (source (graph core2588) (root 10) 0 4) DegreeTwoThreeSpectrum5917.graph sourceMap2588=true := by decide +kernel
theorem fusedMap2588_checked : acceptsGraphIso
    (fused (graph core2588) (root 10) 0 4) DegreeTwoThreeSpectrum5954.graph fusedMap2588=true := by decide +kernel
theorem certified2588 : Certified (graph core2588) (root 10) 0 4 :=
  of_native_maps core2588 DegreeTwoThreeSpectrum5917.graph DegreeTwoThreeSpectrum5954.graph
    sourceMap2588 fusedMap2588 sourceMap2588_checked fusedMap2588_checked
    DegreeTwoThreeFiniteComparisons.comparison2588
#print axioms sourceMap2588_checked
#print axioms fusedMap2588_checked
#print axioms certified2588
def sourceMap2588swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,1,2,3,4,5,10] (sourceLabel 10 4 0 v)
def fusedMap2588swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 4 0 v)
theorem sourceMap2588swap_checked : acceptsGraphIso
    (source (graph core2588) (root 10) 4 0) DegreeTwoThreeSpectrum5917.graph sourceMap2588swap=true := by decide +kernel
theorem fusedMap2588swap_checked : acceptsGraphIso
    (fused (graph core2588) (root 10) 4 0) DegreeTwoThreeSpectrum5954.graph fusedMap2588swap=true := by decide +kernel
theorem certified2588swap : Certified (graph core2588) (root 10) 4 0 :=
  of_native_maps core2588 DegreeTwoThreeSpectrum5917.graph DegreeTwoThreeSpectrum5954.graph
    sourceMap2588swap fusedMap2588swap sourceMap2588swap_checked fusedMap2588swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2588
#print axioms sourceMap2588swap_checked
#print axioms fusedMap2588swap_checked
#print axioms certified2588swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
