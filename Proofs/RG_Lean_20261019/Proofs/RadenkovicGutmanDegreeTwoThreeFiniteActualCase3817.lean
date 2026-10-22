/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3817 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap3817 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3817 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3817_checked : acceptsGraphIso
    (source (graph core3817) (root 7) 1 4) DegreeTwoThreeSpectrum3404.graph sourceMap3817=true := by decide +kernel
theorem fusedMap3817_checked : acceptsGraphIso
    (fused (graph core3817) (root 7) 1 4) DegreeTwoThreeSpectrum2654.graph fusedMap3817=true := by decide +kernel
theorem certified3817 : Certified (graph core3817) (root 7) 1 4 :=
  of_native_maps core3817 DegreeTwoThreeSpectrum3404.graph DegreeTwoThreeSpectrum2654.graph
    sourceMap3817 fusedMap3817 sourceMap3817_checked fusedMap3817_checked
    DegreeTwoThreeFiniteComparisons.comparison3817
#print axioms sourceMap3817_checked
#print axioms fusedMap3817_checked
#print axioms certified3817
def sourceMap3817swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3817swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3817swap_checked : acceptsGraphIso
    (source (graph core3817) (root 7) 4 1) DegreeTwoThreeSpectrum3404.graph sourceMap3817swap=true := by decide +kernel
theorem fusedMap3817swap_checked : acceptsGraphIso
    (fused (graph core3817) (root 7) 4 1) DegreeTwoThreeSpectrum2654.graph fusedMap3817swap=true := by decide +kernel
theorem certified3817swap : Certified (graph core3817) (root 7) 4 1 :=
  of_native_maps core3817 DegreeTwoThreeSpectrum3404.graph DegreeTwoThreeSpectrum2654.graph
    sourceMap3817swap fusedMap3817swap sourceMap3817swap_checked fusedMap3817swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3817
#print axioms sourceMap3817swap_checked
#print axioms fusedMap3817swap_checked
#print axioms certified3817swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
