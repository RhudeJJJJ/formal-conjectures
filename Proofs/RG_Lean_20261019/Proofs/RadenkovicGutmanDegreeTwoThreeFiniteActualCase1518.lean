/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1518 : Family 10 := level10.get ⟨353,by decide⟩
def sourceMap1518 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1518 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1518_checked : acceptsGraphIso
    (source (graph core1518) (root 10) 0 2) DegreeTwoThreeSpectrum2788.graph sourceMap1518=true := by decide +kernel
theorem fusedMap1518_checked : acceptsGraphIso
    (fused (graph core1518) (root 10) 0 2) DegreeTwoThreeSpectrum2793.graph fusedMap1518=true := by decide +kernel
theorem certified1518 : Certified (graph core1518) (root 10) 0 2 :=
  of_native_maps core1518 DegreeTwoThreeSpectrum2788.graph DegreeTwoThreeSpectrum2793.graph
    sourceMap1518 fusedMap1518 sourceMap1518_checked fusedMap1518_checked
    DegreeTwoThreeFiniteComparisons.comparison1518
#print axioms sourceMap1518_checked
#print axioms fusedMap1518_checked
#print axioms certified1518
def sourceMap1518swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1518swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1518swap_checked : acceptsGraphIso
    (source (graph core1518) (root 10) 2 0) DegreeTwoThreeSpectrum2788.graph sourceMap1518swap=true := by decide +kernel
theorem fusedMap1518swap_checked : acceptsGraphIso
    (fused (graph core1518) (root 10) 2 0) DegreeTwoThreeSpectrum2793.graph fusedMap1518swap=true := by decide +kernel
theorem certified1518swap : Certified (graph core1518) (root 10) 2 0 :=
  of_native_maps core1518 DegreeTwoThreeSpectrum2788.graph DegreeTwoThreeSpectrum2793.graph
    sourceMap1518swap fusedMap1518swap sourceMap1518swap_checked fusedMap1518swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1518
#print axioms sourceMap1518swap_checked
#print axioms fusedMap1518swap_checked
#print axioms certified1518swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
