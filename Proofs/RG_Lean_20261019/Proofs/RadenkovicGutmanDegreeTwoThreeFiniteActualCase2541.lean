/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2541 : Family 10 := level10.get ⟨353,by decide⟩
def sourceMap2541 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2541 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2541_checked : acceptsGraphIso
    (source (graph core2541) (root 10) 0 4) DegreeTwoThreeSpectrum5626.graph sourceMap2541=true := by decide +kernel
theorem fusedMap2541_checked : acceptsGraphIso
    (fused (graph core2541) (root 10) 0 4) DegreeTwoThreeSpectrum5628.graph fusedMap2541=true := by decide +kernel
theorem certified2541 : Certified (graph core2541) (root 10) 0 4 :=
  of_native_maps core2541 DegreeTwoThreeSpectrum5626.graph DegreeTwoThreeSpectrum5628.graph
    sourceMap2541 fusedMap2541 sourceMap2541_checked fusedMap2541_checked
    DegreeTwoThreeFiniteComparisons.comparison2541
#print axioms sourceMap2541_checked
#print axioms fusedMap2541_checked
#print axioms certified2541
def sourceMap2541swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2541swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2541swap_checked : acceptsGraphIso
    (source (graph core2541) (root 10) 4 0) DegreeTwoThreeSpectrum5626.graph sourceMap2541swap=true := by decide +kernel
theorem fusedMap2541swap_checked : acceptsGraphIso
    (fused (graph core2541) (root 10) 4 0) DegreeTwoThreeSpectrum5628.graph fusedMap2541swap=true := by decide +kernel
theorem certified2541swap : Certified (graph core2541) (root 10) 4 0 :=
  of_native_maps core2541 DegreeTwoThreeSpectrum5626.graph DegreeTwoThreeSpectrum5628.graph
    sourceMap2541swap fusedMap2541swap sourceMap2541swap_checked fusedMap2541swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2541
#print axioms sourceMap2541swap_checked
#print axioms fusedMap2541swap_checked
#print axioms certified2541swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
