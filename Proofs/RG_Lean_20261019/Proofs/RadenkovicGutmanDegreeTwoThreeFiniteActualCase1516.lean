/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1516 : Family 10 := level10.get ⟨349,by decide⟩
def sourceMap1516 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1516 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1516_checked : acceptsGraphIso
    (source (graph core1516) (root 10) 0 2) DegreeTwoThreeSpectrum2785.graph sourceMap1516=true := by decide +kernel
theorem fusedMap1516_checked : acceptsGraphIso
    (fused (graph core1516) (root 10) 0 2) DegreeTwoThreeSpectrum2787.graph fusedMap1516=true := by decide +kernel
theorem certified1516 : Certified (graph core1516) (root 10) 0 2 :=
  of_native_maps core1516 DegreeTwoThreeSpectrum2785.graph DegreeTwoThreeSpectrum2787.graph
    sourceMap1516 fusedMap1516 sourceMap1516_checked fusedMap1516_checked
    DegreeTwoThreeFiniteComparisons.comparison1516
#print axioms sourceMap1516_checked
#print axioms fusedMap1516_checked
#print axioms certified1516
def sourceMap1516swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1516swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1516swap_checked : acceptsGraphIso
    (source (graph core1516) (root 10) 2 0) DegreeTwoThreeSpectrum2785.graph sourceMap1516swap=true := by decide +kernel
theorem fusedMap1516swap_checked : acceptsGraphIso
    (fused (graph core1516) (root 10) 2 0) DegreeTwoThreeSpectrum2787.graph fusedMap1516swap=true := by decide +kernel
theorem certified1516swap : Certified (graph core1516) (root 10) 2 0 :=
  of_native_maps core1516 DegreeTwoThreeSpectrum2785.graph DegreeTwoThreeSpectrum2787.graph
    sourceMap1516swap fusedMap1516swap sourceMap1516swap_checked fusedMap1516swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1516
#print axioms sourceMap1516swap_checked
#print axioms fusedMap1516swap_checked
#print axioms certified1516swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
