/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2556 : Family 10 := level10.get ⟨401,by decide⟩
def sourceMap2556 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2556 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2556_checked : acceptsGraphIso
    (source (graph core2556) (root 10) 0 4) DegreeTwoThreeSpectrum5756.graph sourceMap2556=true := by decide +kernel
theorem fusedMap2556_checked : acceptsGraphIso
    (fused (graph core2556) (root 10) 0 4) DegreeTwoThreeSpectrum5758.graph fusedMap2556=true := by decide +kernel
theorem certified2556 : Certified (graph core2556) (root 10) 0 4 :=
  of_native_maps core2556 DegreeTwoThreeSpectrum5756.graph DegreeTwoThreeSpectrum5758.graph
    sourceMap2556 fusedMap2556 sourceMap2556_checked fusedMap2556_checked
    DegreeTwoThreeFiniteComparisons.comparison2556
#print axioms sourceMap2556_checked
#print axioms fusedMap2556_checked
#print axioms certified2556
def sourceMap2556swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2556swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2556swap_checked : acceptsGraphIso
    (source (graph core2556) (root 10) 4 0) DegreeTwoThreeSpectrum5756.graph sourceMap2556swap=true := by decide +kernel
theorem fusedMap2556swap_checked : acceptsGraphIso
    (fused (graph core2556) (root 10) 4 0) DegreeTwoThreeSpectrum5758.graph fusedMap2556swap=true := by decide +kernel
theorem certified2556swap : Certified (graph core2556) (root 10) 4 0 :=
  of_native_maps core2556 DegreeTwoThreeSpectrum5756.graph DegreeTwoThreeSpectrum5758.graph
    sourceMap2556swap fusedMap2556swap sourceMap2556swap_checked fusedMap2556swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2556
#print axioms sourceMap2556swap_checked
#print axioms fusedMap2556swap_checked
#print axioms certified2556swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
