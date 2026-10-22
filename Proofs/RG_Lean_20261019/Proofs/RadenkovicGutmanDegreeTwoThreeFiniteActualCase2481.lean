/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2481 : Family 10 := level10.get ⟨142,by decide⟩
def sourceMap2481 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,15,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2481 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2481_checked : acceptsGraphIso
    (source (graph core2481) (root 10) 0 4) DegreeTwoThreeSpectrum5814.graph sourceMap2481=true := by decide +kernel
theorem fusedMap2481_checked : acceptsGraphIso
    (fused (graph core2481) (root 10) 0 4) DegreeTwoThreeSpectrum5074.graph fusedMap2481=true := by decide +kernel
theorem certified2481 : Certified (graph core2481) (root 10) 0 4 :=
  of_native_maps core2481 DegreeTwoThreeSpectrum5814.graph DegreeTwoThreeSpectrum5074.graph
    sourceMap2481 fusedMap2481 sourceMap2481_checked fusedMap2481_checked
    DegreeTwoThreeFiniteComparisons.comparison2481
#print axioms sourceMap2481_checked
#print axioms fusedMap2481_checked
#print axioms certified2481
def sourceMap2481swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,9,10,11,12,13,15] (sourceLabel 10 4 0 v)
def fusedMap2481swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2481swap_checked : acceptsGraphIso
    (source (graph core2481) (root 10) 4 0) DegreeTwoThreeSpectrum5814.graph sourceMap2481swap=true := by decide +kernel
theorem fusedMap2481swap_checked : acceptsGraphIso
    (fused (graph core2481) (root 10) 4 0) DegreeTwoThreeSpectrum5074.graph fusedMap2481swap=true := by decide +kernel
theorem certified2481swap : Certified (graph core2481) (root 10) 4 0 :=
  of_native_maps core2481 DegreeTwoThreeSpectrum5814.graph DegreeTwoThreeSpectrum5074.graph
    sourceMap2481swap fusedMap2481swap sourceMap2481swap_checked fusedMap2481swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2481
#print axioms sourceMap2481swap_checked
#print axioms fusedMap2481swap_checked
#print axioms certified2481swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
