/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2491 : Family 10 := level10.get ⟨175,by decide⟩
def sourceMap2491 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,7,8,9,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2491 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2491_checked : acceptsGraphIso
    (source (graph core2491) (root 10) 0 4) DegreeTwoThreeSpectrum5939.graph sourceMap2491=true := by decide +kernel
theorem fusedMap2491_checked : acceptsGraphIso
    (fused (graph core2491) (root 10) 0 4) DegreeTwoThreeSpectrum5120.graph fusedMap2491=true := by decide +kernel
theorem certified2491 : Certified (graph core2491) (root 10) 0 4 :=
  of_native_maps core2491 DegreeTwoThreeSpectrum5939.graph DegreeTwoThreeSpectrum5120.graph
    sourceMap2491 fusedMap2491 sourceMap2491_checked fusedMap2491_checked
    DegreeTwoThreeFiniteComparisons.comparison2491
#print axioms sourceMap2491_checked
#print axioms fusedMap2491_checked
#print axioms certified2491
def sourceMap2491swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,7,8,2,3,4,5,6,9] (sourceLabel 10 4 0 v)
def fusedMap2491swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2491swap_checked : acceptsGraphIso
    (source (graph core2491) (root 10) 4 0) DegreeTwoThreeSpectrum5939.graph sourceMap2491swap=true := by decide +kernel
theorem fusedMap2491swap_checked : acceptsGraphIso
    (fused (graph core2491) (root 10) 4 0) DegreeTwoThreeSpectrum5120.graph fusedMap2491swap=true := by decide +kernel
theorem certified2491swap : Certified (graph core2491) (root 10) 4 0 :=
  of_native_maps core2491 DegreeTwoThreeSpectrum5939.graph DegreeTwoThreeSpectrum5120.graph
    sourceMap2491swap fusedMap2491swap sourceMap2491swap_checked fusedMap2491swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2491
#print axioms sourceMap2491swap_checked
#print axioms fusedMap2491swap_checked
#print axioms certified2491swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
