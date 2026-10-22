/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2498 : Family 10 := level10.get ⟨200,by decide⟩
def sourceMap2498 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2498 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2498_checked : acceptsGraphIso
    (source (graph core2498) (root 10) 0 4) DegreeTwoThreeSpectrum5181.graph sourceMap2498=true := by decide +kernel
theorem fusedMap2498_checked : acceptsGraphIso
    (fused (graph core2498) (root 10) 0 4) DegreeTwoThreeSpectrum5182.graph fusedMap2498=true := by decide +kernel
theorem certified2498 : Certified (graph core2498) (root 10) 0 4 :=
  of_native_maps core2498 DegreeTwoThreeSpectrum5181.graph DegreeTwoThreeSpectrum5182.graph
    sourceMap2498 fusedMap2498 sourceMap2498_checked fusedMap2498_checked
    DegreeTwoThreeFiniteComparisons.comparison2498
#print axioms sourceMap2498_checked
#print axioms fusedMap2498_checked
#print axioms certified2498
def sourceMap2498swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2498swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2498swap_checked : acceptsGraphIso
    (source (graph core2498) (root 10) 4 0) DegreeTwoThreeSpectrum5181.graph sourceMap2498swap=true := by decide +kernel
theorem fusedMap2498swap_checked : acceptsGraphIso
    (fused (graph core2498) (root 10) 4 0) DegreeTwoThreeSpectrum5182.graph fusedMap2498swap=true := by decide +kernel
theorem certified2498swap : Certified (graph core2498) (root 10) 4 0 :=
  of_native_maps core2498 DegreeTwoThreeSpectrum5181.graph DegreeTwoThreeSpectrum5182.graph
    sourceMap2498swap fusedMap2498swap sourceMap2498swap_checked fusedMap2498swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2498
#print axioms sourceMap2498swap_checked
#print axioms fusedMap2498swap_checked
#print axioms certified2498swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
