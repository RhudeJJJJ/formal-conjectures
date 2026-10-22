/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2477 : Family 10 := level10.get ⟨125,by decide⟩
def sourceMap2477 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2477 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2477_checked : acceptsGraphIso
    (source (graph core2477) (root 10) 0 4) DegreeTwoThreeSpectrum5723.graph sourceMap2477=true := by decide +kernel
theorem fusedMap2477_checked : acceptsGraphIso
    (fused (graph core2477) (root 10) 0 4) DegreeTwoThreeSpectrum5054.graph fusedMap2477=true := by decide +kernel
theorem certified2477 : Certified (graph core2477) (root 10) 0 4 :=
  of_native_maps core2477 DegreeTwoThreeSpectrum5723.graph DegreeTwoThreeSpectrum5054.graph
    sourceMap2477 fusedMap2477 sourceMap2477_checked fusedMap2477_checked
    DegreeTwoThreeFiniteComparisons.comparison2477
#print axioms sourceMap2477_checked
#print axioms fusedMap2477_checked
#print axioms certified2477
def sourceMap2477swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2477swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2477swap_checked : acceptsGraphIso
    (source (graph core2477) (root 10) 4 0) DegreeTwoThreeSpectrum5723.graph sourceMap2477swap=true := by decide +kernel
theorem fusedMap2477swap_checked : acceptsGraphIso
    (fused (graph core2477) (root 10) 4 0) DegreeTwoThreeSpectrum5054.graph fusedMap2477swap=true := by decide +kernel
theorem certified2477swap : Certified (graph core2477) (root 10) 4 0 :=
  of_native_maps core2477 DegreeTwoThreeSpectrum5723.graph DegreeTwoThreeSpectrum5054.graph
    sourceMap2477swap fusedMap2477swap sourceMap2477swap_checked fusedMap2477swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2477
#print axioms sourceMap2477swap_checked
#print axioms fusedMap2477swap_checked
#print axioms certified2477swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
