/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2532 : Family 10 := level10.get ⟨321,by decide⟩
def sourceMap2532 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2532 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2532_checked : acceptsGraphIso
    (source (graph core2532) (root 10) 0 4) DegreeTwoThreeSpectrum5536.graph sourceMap2532=true := by decide +kernel
theorem fusedMap2532_checked : acceptsGraphIso
    (fused (graph core2532) (root 10) 0 4) DegreeTwoThreeSpectrum5538.graph fusedMap2532=true := by decide +kernel
theorem certified2532 : Certified (graph core2532) (root 10) 0 4 :=
  of_native_maps core2532 DegreeTwoThreeSpectrum5536.graph DegreeTwoThreeSpectrum5538.graph
    sourceMap2532 fusedMap2532 sourceMap2532_checked fusedMap2532_checked
    DegreeTwoThreeFiniteComparisons.comparison2532
#print axioms sourceMap2532_checked
#print axioms fusedMap2532_checked
#print axioms certified2532
def sourceMap2532swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2532swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2532swap_checked : acceptsGraphIso
    (source (graph core2532) (root 10) 4 0) DegreeTwoThreeSpectrum5536.graph sourceMap2532swap=true := by decide +kernel
theorem fusedMap2532swap_checked : acceptsGraphIso
    (fused (graph core2532) (root 10) 4 0) DegreeTwoThreeSpectrum5538.graph fusedMap2532swap=true := by decide +kernel
theorem certified2532swap : Certified (graph core2532) (root 10) 4 0 :=
  of_native_maps core2532 DegreeTwoThreeSpectrum5536.graph DegreeTwoThreeSpectrum5538.graph
    sourceMap2532swap fusedMap2532swap sourceMap2532swap_checked fusedMap2532swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2532
#print axioms sourceMap2532swap_checked
#print axioms fusedMap2532swap_checked
#print axioms certified2532swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
