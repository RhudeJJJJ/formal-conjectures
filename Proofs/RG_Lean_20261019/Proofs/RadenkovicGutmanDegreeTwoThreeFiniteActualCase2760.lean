/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2760 : Family 10 := level10.get ⟨968,by decide⟩
def sourceMap2760 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2760 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2760_checked : acceptsGraphIso
    (source (graph core2760) (root 10) 0 4) DegreeTwoThreeSpectrum7038.graph sourceMap2760=true := by decide +kernel
theorem fusedMap2760_checked : acceptsGraphIso
    (fused (graph core2760) (root 10) 0 4) DegreeTwoThreeSpectrum5887.graph fusedMap2760=true := by decide +kernel
theorem certified2760 : Certified (graph core2760) (root 10) 0 4 :=
  of_native_maps core2760 DegreeTwoThreeSpectrum7038.graph DegreeTwoThreeSpectrum5887.graph
    sourceMap2760 fusedMap2760 sourceMap2760_checked fusedMap2760_checked
    DegreeTwoThreeFiniteComparisons.comparison2760
#print axioms sourceMap2760_checked
#print axioms fusedMap2760_checked
#print axioms certified2760
def sourceMap2760swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2760swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2760swap_checked : acceptsGraphIso
    (source (graph core2760) (root 10) 4 0) DegreeTwoThreeSpectrum7038.graph sourceMap2760swap=true := by decide +kernel
theorem fusedMap2760swap_checked : acceptsGraphIso
    (fused (graph core2760) (root 10) 4 0) DegreeTwoThreeSpectrum5887.graph fusedMap2760swap=true := by decide +kernel
theorem certified2760swap : Certified (graph core2760) (root 10) 4 0 :=
  of_native_maps core2760 DegreeTwoThreeSpectrum7038.graph DegreeTwoThreeSpectrum5887.graph
    sourceMap2760swap fusedMap2760swap sourceMap2760swap_checked fusedMap2760swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2760
#print axioms sourceMap2760swap_checked
#print axioms fusedMap2760swap_checked
#print axioms certified2760swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
