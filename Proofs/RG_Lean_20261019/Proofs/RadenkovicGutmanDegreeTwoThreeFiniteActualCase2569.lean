/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2569 : Family 10 := level10.get ⟨444,by decide⟩
def sourceMap2569 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2569 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2569_checked : acceptsGraphIso
    (source (graph core2569) (root 10) 0 4) DegreeTwoThreeSpectrum5862.graph sourceMap2569=true := by decide +kernel
theorem fusedMap2569_checked : acceptsGraphIso
    (fused (graph core2569) (root 10) 0 4) DegreeTwoThreeSpectrum5863.graph fusedMap2569=true := by decide +kernel
theorem certified2569 : Certified (graph core2569) (root 10) 0 4 :=
  of_native_maps core2569 DegreeTwoThreeSpectrum5862.graph DegreeTwoThreeSpectrum5863.graph
    sourceMap2569 fusedMap2569 sourceMap2569_checked fusedMap2569_checked
    DegreeTwoThreeFiniteComparisons.comparison2569
#print axioms sourceMap2569_checked
#print axioms fusedMap2569_checked
#print axioms certified2569
def sourceMap2569swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2569swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2569swap_checked : acceptsGraphIso
    (source (graph core2569) (root 10) 4 0) DegreeTwoThreeSpectrum5862.graph sourceMap2569swap=true := by decide +kernel
theorem fusedMap2569swap_checked : acceptsGraphIso
    (fused (graph core2569) (root 10) 4 0) DegreeTwoThreeSpectrum5863.graph fusedMap2569swap=true := by decide +kernel
theorem certified2569swap : Certified (graph core2569) (root 10) 4 0 :=
  of_native_maps core2569 DegreeTwoThreeSpectrum5862.graph DegreeTwoThreeSpectrum5863.graph
    sourceMap2569swap fusedMap2569swap sourceMap2569swap_checked fusedMap2569swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2569
#print axioms sourceMap2569swap_checked
#print axioms fusedMap2569swap_checked
#print axioms certified2569swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
