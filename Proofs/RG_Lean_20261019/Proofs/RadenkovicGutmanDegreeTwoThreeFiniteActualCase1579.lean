/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1579 : Family 10 := level10.get ⟨541,by decide⟩
def sourceMap1579 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1579 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1579_checked : acceptsGraphIso
    (source (graph core1579) (root 10) 0 2) DegreeTwoThreeSpectrum3135.graph sourceMap1579=true := by decide +kernel
theorem fusedMap1579_checked : acceptsGraphIso
    (fused (graph core1579) (root 10) 0 2) DegreeTwoThreeSpectrum2478.graph fusedMap1579=true := by decide +kernel
theorem certified1579 : Certified (graph core1579) (root 10) 0 2 :=
  of_native_maps core1579 DegreeTwoThreeSpectrum3135.graph DegreeTwoThreeSpectrum2478.graph
    sourceMap1579 fusedMap1579 sourceMap1579_checked fusedMap1579_checked
    DegreeTwoThreeFiniteComparisons.comparison1579
#print axioms sourceMap1579_checked
#print axioms fusedMap1579_checked
#print axioms certified1579
def sourceMap1579swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1579swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1579swap_checked : acceptsGraphIso
    (source (graph core1579) (root 10) 2 0) DegreeTwoThreeSpectrum3135.graph sourceMap1579swap=true := by decide +kernel
theorem fusedMap1579swap_checked : acceptsGraphIso
    (fused (graph core1579) (root 10) 2 0) DegreeTwoThreeSpectrum2478.graph fusedMap1579swap=true := by decide +kernel
theorem certified1579swap : Certified (graph core1579) (root 10) 2 0 :=
  of_native_maps core1579 DegreeTwoThreeSpectrum3135.graph DegreeTwoThreeSpectrum2478.graph
    sourceMap1579swap fusedMap1579swap sourceMap1579swap_checked fusedMap1579swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1579
#print axioms sourceMap1579swap_checked
#print axioms fusedMap1579swap_checked
#print axioms certified1579swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
