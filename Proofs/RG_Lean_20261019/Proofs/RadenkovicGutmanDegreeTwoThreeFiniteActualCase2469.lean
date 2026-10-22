/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2469 : Family 10 := level10.get ⟨85,by decide⟩
def sourceMap2469 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2469 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2469_checked : acceptsGraphIso
    (source (graph core2469) (root 10) 0 4) DegreeTwoThreeSpectrum5416.graph sourceMap2469=true := by decide +kernel
theorem fusedMap2469_checked : acceptsGraphIso
    (fused (graph core2469) (root 10) 0 4) DegreeTwoThreeSpectrum5004.graph fusedMap2469=true := by decide +kernel
theorem certified2469 : Certified (graph core2469) (root 10) 0 4 :=
  of_native_maps core2469 DegreeTwoThreeSpectrum5416.graph DegreeTwoThreeSpectrum5004.graph
    sourceMap2469 fusedMap2469 sourceMap2469_checked fusedMap2469_checked
    DegreeTwoThreeFiniteComparisons.comparison2469
#print axioms sourceMap2469_checked
#print axioms fusedMap2469_checked
#print axioms certified2469
def sourceMap2469swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2469swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2469swap_checked : acceptsGraphIso
    (source (graph core2469) (root 10) 4 0) DegreeTwoThreeSpectrum5416.graph sourceMap2469swap=true := by decide +kernel
theorem fusedMap2469swap_checked : acceptsGraphIso
    (fused (graph core2469) (root 10) 4 0) DegreeTwoThreeSpectrum5004.graph fusedMap2469swap=true := by decide +kernel
theorem certified2469swap : Certified (graph core2469) (root 10) 4 0 :=
  of_native_maps core2469 DegreeTwoThreeSpectrum5416.graph DegreeTwoThreeSpectrum5004.graph
    sourceMap2469swap fusedMap2469swap sourceMap2469swap_checked fusedMap2469swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2469
#print axioms sourceMap2469swap_checked
#print axioms fusedMap2469swap_checked
#print axioms certified2469swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
