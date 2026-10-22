/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2939 : Family 10 := level10.get ⟨1411,by decide⟩
def sourceMap2939 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2939 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2939_checked : acceptsGraphIso
    (source (graph core2939) (root 10) 0 4) DegreeTwoThreeSpectrum6821.graph sourceMap2939=true := by decide +kernel
theorem fusedMap2939_checked : acceptsGraphIso
    (fused (graph core2939) (root 10) 0 4) DegreeTwoThreeSpectrum6824.graph fusedMap2939=true := by decide +kernel
theorem certified2939 : Certified (graph core2939) (root 10) 0 4 :=
  of_native_maps core2939 DegreeTwoThreeSpectrum6821.graph DegreeTwoThreeSpectrum6824.graph
    sourceMap2939 fusedMap2939 sourceMap2939_checked fusedMap2939_checked
    DegreeTwoThreeFiniteComparisons.comparison2939
#print axioms sourceMap2939_checked
#print axioms fusedMap2939_checked
#print axioms certified2939
def sourceMap2939swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2939swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2939swap_checked : acceptsGraphIso
    (source (graph core2939) (root 10) 4 0) DegreeTwoThreeSpectrum6821.graph sourceMap2939swap=true := by decide +kernel
theorem fusedMap2939swap_checked : acceptsGraphIso
    (fused (graph core2939) (root 10) 4 0) DegreeTwoThreeSpectrum6824.graph fusedMap2939swap=true := by decide +kernel
theorem certified2939swap : Certified (graph core2939) (root 10) 4 0 :=
  of_native_maps core2939 DegreeTwoThreeSpectrum6821.graph DegreeTwoThreeSpectrum6824.graph
    sourceMap2939swap fusedMap2939swap sourceMap2939swap_checked fusedMap2939swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2939
#print axioms sourceMap2939swap_checked
#print axioms fusedMap2939swap_checked
#print axioms certified2939swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
