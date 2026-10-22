/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2535 : Family 10 := level10.get ⟨336,by decide⟩
def sourceMap2535 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2535 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2535_checked : acceptsGraphIso
    (source (graph core2535) (root 10) 0 4) DegreeTwoThreeSpectrum5583.graph sourceMap2535=true := by decide +kernel
theorem fusedMap2535_checked : acceptsGraphIso
    (fused (graph core2535) (root 10) 0 4) DegreeTwoThreeSpectrum5584.graph fusedMap2535=true := by decide +kernel
theorem certified2535 : Certified (graph core2535) (root 10) 0 4 :=
  of_native_maps core2535 DegreeTwoThreeSpectrum5583.graph DegreeTwoThreeSpectrum5584.graph
    sourceMap2535 fusedMap2535 sourceMap2535_checked fusedMap2535_checked
    DegreeTwoThreeFiniteComparisons.comparison2535
#print axioms sourceMap2535_checked
#print axioms fusedMap2535_checked
#print axioms certified2535
def sourceMap2535swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2535swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2535swap_checked : acceptsGraphIso
    (source (graph core2535) (root 10) 4 0) DegreeTwoThreeSpectrum5583.graph sourceMap2535swap=true := by decide +kernel
theorem fusedMap2535swap_checked : acceptsGraphIso
    (fused (graph core2535) (root 10) 4 0) DegreeTwoThreeSpectrum5584.graph fusedMap2535swap=true := by decide +kernel
theorem certified2535swap : Certified (graph core2535) (root 10) 4 0 :=
  of_native_maps core2535 DegreeTwoThreeSpectrum5583.graph DegreeTwoThreeSpectrum5584.graph
    sourceMap2535swap fusedMap2535swap sourceMap2535swap_checked fusedMap2535swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2535
#print axioms sourceMap2535swap_checked
#print axioms fusedMap2535swap_checked
#print axioms certified2535swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
