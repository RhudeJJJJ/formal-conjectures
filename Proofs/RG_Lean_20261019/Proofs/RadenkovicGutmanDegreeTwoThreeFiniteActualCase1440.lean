/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1440 : Family 10 := level10.get ⟨59,by decide⟩
def sourceMap1440 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1440 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1440_checked : acceptsGraphIso
    (source (graph core1440) (root 10) 0 2) DegreeTwoThreeSpectrum2496.graph sourceMap1440=true := by decide +kernel
theorem fusedMap1440_checked : acceptsGraphIso
    (fused (graph core1440) (root 10) 0 2) DegreeTwoThreeSpectrum2319.graph fusedMap1440=true := by decide +kernel
theorem certified1440 : Certified (graph core1440) (root 10) 0 2 :=
  of_native_maps core1440 DegreeTwoThreeSpectrum2496.graph DegreeTwoThreeSpectrum2319.graph
    sourceMap1440 fusedMap1440 sourceMap1440_checked fusedMap1440_checked
    DegreeTwoThreeFiniteComparisons.comparison1440
#print axioms sourceMap1440_checked
#print axioms fusedMap1440_checked
#print axioms certified1440
def sourceMap1440swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1440swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1440swap_checked : acceptsGraphIso
    (source (graph core1440) (root 10) 2 0) DegreeTwoThreeSpectrum2496.graph sourceMap1440swap=true := by decide +kernel
theorem fusedMap1440swap_checked : acceptsGraphIso
    (fused (graph core1440) (root 10) 2 0) DegreeTwoThreeSpectrum2319.graph fusedMap1440swap=true := by decide +kernel
theorem certified1440swap : Certified (graph core1440) (root 10) 2 0 :=
  of_native_maps core1440 DegreeTwoThreeSpectrum2496.graph DegreeTwoThreeSpectrum2319.graph
    sourceMap1440swap fusedMap1440swap sourceMap1440swap_checked fusedMap1440swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1440
#print axioms sourceMap1440swap_checked
#print axioms fusedMap1440swap_checked
#print axioms certified1440swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
