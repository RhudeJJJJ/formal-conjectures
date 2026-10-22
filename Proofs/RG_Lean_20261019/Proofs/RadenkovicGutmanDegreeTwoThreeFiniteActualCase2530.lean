/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2530 : Family 10 := level10.get ⟨317,by decide⟩
def sourceMap2530 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2530 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2530_checked : acceptsGraphIso
    (source (graph core2530) (root 10) 0 4) DegreeTwoThreeSpectrum5527.graph sourceMap2530=true := by decide +kernel
theorem fusedMap2530_checked : acceptsGraphIso
    (fused (graph core2530) (root 10) 0 4) DegreeTwoThreeSpectrum5528.graph fusedMap2530=true := by decide +kernel
theorem certified2530 : Certified (graph core2530) (root 10) 0 4 :=
  of_native_maps core2530 DegreeTwoThreeSpectrum5527.graph DegreeTwoThreeSpectrum5528.graph
    sourceMap2530 fusedMap2530 sourceMap2530_checked fusedMap2530_checked
    DegreeTwoThreeFiniteComparisons.comparison2530
#print axioms sourceMap2530_checked
#print axioms fusedMap2530_checked
#print axioms certified2530
def sourceMap2530swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2530swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2530swap_checked : acceptsGraphIso
    (source (graph core2530) (root 10) 4 0) DegreeTwoThreeSpectrum5527.graph sourceMap2530swap=true := by decide +kernel
theorem fusedMap2530swap_checked : acceptsGraphIso
    (fused (graph core2530) (root 10) 4 0) DegreeTwoThreeSpectrum5528.graph fusedMap2530swap=true := by decide +kernel
theorem certified2530swap : Certified (graph core2530) (root 10) 4 0 :=
  of_native_maps core2530 DegreeTwoThreeSpectrum5527.graph DegreeTwoThreeSpectrum5528.graph
    sourceMap2530swap fusedMap2530swap sourceMap2530swap_checked fusedMap2530swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2530
#print axioms sourceMap2530swap_checked
#print axioms fusedMap2530swap_checked
#print axioms certified2530swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
