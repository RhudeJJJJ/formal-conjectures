/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2686 : Family 10 := level10.get ⟨785,by decide⟩
def sourceMap2686 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2686 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2686_checked : acceptsGraphIso
    (source (graph core2686) (root 10) 0 4) DegreeTwoThreeSpectrum6724.graph sourceMap2686=true := by decide +kernel
theorem fusedMap2686_checked : acceptsGraphIso
    (fused (graph core2686) (root 10) 0 4) DegreeTwoThreeSpectrum5566.graph fusedMap2686=true := by decide +kernel
theorem certified2686 : Certified (graph core2686) (root 10) 0 4 :=
  of_native_maps core2686 DegreeTwoThreeSpectrum6724.graph DegreeTwoThreeSpectrum5566.graph
    sourceMap2686 fusedMap2686 sourceMap2686_checked fusedMap2686_checked
    DegreeTwoThreeFiniteComparisons.comparison2686
#print axioms sourceMap2686_checked
#print axioms fusedMap2686_checked
#print axioms certified2686
def sourceMap2686swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2686swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2686swap_checked : acceptsGraphIso
    (source (graph core2686) (root 10) 4 0) DegreeTwoThreeSpectrum6724.graph sourceMap2686swap=true := by decide +kernel
theorem fusedMap2686swap_checked : acceptsGraphIso
    (fused (graph core2686) (root 10) 4 0) DegreeTwoThreeSpectrum5566.graph fusedMap2686swap=true := by decide +kernel
theorem certified2686swap : Certified (graph core2686) (root 10) 4 0 :=
  of_native_maps core2686 DegreeTwoThreeSpectrum6724.graph DegreeTwoThreeSpectrum5566.graph
    sourceMap2686swap fusedMap2686swap sourceMap2686swap_checked fusedMap2686swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2686
#print axioms sourceMap2686swap_checked
#print axioms fusedMap2686swap_checked
#print axioms certified2686swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
