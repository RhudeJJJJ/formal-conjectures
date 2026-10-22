/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2771 : Family 10 := level10.get ⟨998,by decide⟩
def sourceMap2771 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2771 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2771_checked : acceptsGraphIso
    (source (graph core2771) (root 10) 0 4) DegreeTwoThreeSpectrum5969.graph sourceMap2771=true := by decide +kernel
theorem fusedMap2771_checked : acceptsGraphIso
    (fused (graph core2771) (root 10) 0 4) DegreeTwoThreeSpectrum5970.graph fusedMap2771=true := by decide +kernel
theorem certified2771 : Certified (graph core2771) (root 10) 0 4 :=
  of_native_maps core2771 DegreeTwoThreeSpectrum5969.graph DegreeTwoThreeSpectrum5970.graph
    sourceMap2771 fusedMap2771 sourceMap2771_checked fusedMap2771_checked
    DegreeTwoThreeFiniteComparisons.comparison2771
#print axioms sourceMap2771_checked
#print axioms fusedMap2771_checked
#print axioms certified2771
def sourceMap2771swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2771swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2771swap_checked : acceptsGraphIso
    (source (graph core2771) (root 10) 4 0) DegreeTwoThreeSpectrum5969.graph sourceMap2771swap=true := by decide +kernel
theorem fusedMap2771swap_checked : acceptsGraphIso
    (fused (graph core2771) (root 10) 4 0) DegreeTwoThreeSpectrum5970.graph fusedMap2771swap=true := by decide +kernel
theorem certified2771swap : Certified (graph core2771) (root 10) 4 0 :=
  of_native_maps core2771 DegreeTwoThreeSpectrum5969.graph DegreeTwoThreeSpectrum5970.graph
    sourceMap2771swap fusedMap2771swap sourceMap2771swap_checked fusedMap2771swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2771
#print axioms sourceMap2771swap_checked
#print axioms fusedMap2771swap_checked
#print axioms certified2771swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
