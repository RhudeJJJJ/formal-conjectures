/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2460 : Family 10 := level10.get ⟨47,by decide⟩
def sourceMap2460 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2460 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 0 4 v)
theorem sourceMap2460_checked : acceptsGraphIso
    (source (graph core2460) (root 10) 0 4) DegreeTwoThreeSpectrum5114.graph sourceMap2460=true := by decide +kernel
theorem fusedMap2460_checked : acceptsGraphIso
    (fused (graph core2460) (root 10) 0 4) DegreeTwoThreeSpectrum5131.graph fusedMap2460=true := by decide +kernel
theorem certified2460 : Certified (graph core2460) (root 10) 0 4 :=
  of_native_maps core2460 DegreeTwoThreeSpectrum5114.graph DegreeTwoThreeSpectrum5131.graph
    sourceMap2460 fusedMap2460 sourceMap2460_checked fusedMap2460_checked
    DegreeTwoThreeFiniteComparisons.comparison2460
#print axioms sourceMap2460_checked
#print axioms fusedMap2460_checked
#print axioms certified2460
def sourceMap2460swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2460swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 4 0 v)
theorem sourceMap2460swap_checked : acceptsGraphIso
    (source (graph core2460) (root 10) 4 0) DegreeTwoThreeSpectrum5114.graph sourceMap2460swap=true := by decide +kernel
theorem fusedMap2460swap_checked : acceptsGraphIso
    (fused (graph core2460) (root 10) 4 0) DegreeTwoThreeSpectrum5131.graph fusedMap2460swap=true := by decide +kernel
theorem certified2460swap : Certified (graph core2460) (root 10) 4 0 :=
  of_native_maps core2460 DegreeTwoThreeSpectrum5114.graph DegreeTwoThreeSpectrum5131.graph
    sourceMap2460swap fusedMap2460swap sourceMap2460swap_checked fusedMap2460swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2460
#print axioms sourceMap2460swap_checked
#print axioms fusedMap2460swap_checked
#print axioms certified2460swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
