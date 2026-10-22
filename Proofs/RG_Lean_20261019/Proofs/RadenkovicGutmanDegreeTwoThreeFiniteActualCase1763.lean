/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1763 : Family 10 := level10.get ⟨1042,by decide⟩
def sourceMap1763 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1763 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1763_checked : acceptsGraphIso
    (source (graph core1763) (root 10) 0 2) DegreeTwoThreeSpectrum3077.graph sourceMap1763=true := by decide +kernel
theorem fusedMap1763_checked : acceptsGraphIso
    (fused (graph core1763) (root 10) 0 2) DegreeTwoThreeSpectrum3078.graph fusedMap1763=true := by decide +kernel
theorem certified1763 : Certified (graph core1763) (root 10) 0 2 :=
  of_native_maps core1763 DegreeTwoThreeSpectrum3077.graph DegreeTwoThreeSpectrum3078.graph
    sourceMap1763 fusedMap1763 sourceMap1763_checked fusedMap1763_checked
    DegreeTwoThreeFiniteComparisons.comparison1763
#print axioms sourceMap1763_checked
#print axioms fusedMap1763_checked
#print axioms certified1763
def sourceMap1763swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1763swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1763swap_checked : acceptsGraphIso
    (source (graph core1763) (root 10) 2 0) DegreeTwoThreeSpectrum3077.graph sourceMap1763swap=true := by decide +kernel
theorem fusedMap1763swap_checked : acceptsGraphIso
    (fused (graph core1763) (root 10) 2 0) DegreeTwoThreeSpectrum3078.graph fusedMap1763swap=true := by decide +kernel
theorem certified1763swap : Certified (graph core1763) (root 10) 2 0 :=
  of_native_maps core1763 DegreeTwoThreeSpectrum3077.graph DegreeTwoThreeSpectrum3078.graph
    sourceMap1763swap fusedMap1763swap sourceMap1763swap_checked fusedMap1763swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1763
#print axioms sourceMap1763swap_checked
#print axioms fusedMap1763swap_checked
#print axioms certified1763swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
