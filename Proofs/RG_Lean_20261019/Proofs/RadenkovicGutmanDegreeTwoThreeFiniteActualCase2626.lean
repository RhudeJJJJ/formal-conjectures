/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2626 : Family 10 := level10.get ⟨611,by decide⟩
def sourceMap2626 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2626 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2626_checked : acceptsGraphIso
    (source (graph core2626) (root 10) 0 4) DegreeTwoThreeSpectrum6333.graph sourceMap2626=true := by decide +kernel
theorem fusedMap2626_checked : acceptsGraphIso
    (fused (graph core2626) (root 10) 0 4) DegreeTwoThreeSpectrum5294.graph fusedMap2626=true := by decide +kernel
theorem certified2626 : Certified (graph core2626) (root 10) 0 4 :=
  of_native_maps core2626 DegreeTwoThreeSpectrum6333.graph DegreeTwoThreeSpectrum5294.graph
    sourceMap2626 fusedMap2626 sourceMap2626_checked fusedMap2626_checked
    DegreeTwoThreeFiniteComparisons.comparison2626
#print axioms sourceMap2626_checked
#print axioms fusedMap2626_checked
#print axioms certified2626
def sourceMap2626swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2626swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2626swap_checked : acceptsGraphIso
    (source (graph core2626) (root 10) 4 0) DegreeTwoThreeSpectrum6333.graph sourceMap2626swap=true := by decide +kernel
theorem fusedMap2626swap_checked : acceptsGraphIso
    (fused (graph core2626) (root 10) 4 0) DegreeTwoThreeSpectrum5294.graph fusedMap2626swap=true := by decide +kernel
theorem certified2626swap : Certified (graph core2626) (root 10) 4 0 :=
  of_native_maps core2626 DegreeTwoThreeSpectrum6333.graph DegreeTwoThreeSpectrum5294.graph
    sourceMap2626swap fusedMap2626swap sourceMap2626swap_checked fusedMap2626swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2626
#print axioms sourceMap2626swap_checked
#print axioms fusedMap2626swap_checked
#print axioms certified2626swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
