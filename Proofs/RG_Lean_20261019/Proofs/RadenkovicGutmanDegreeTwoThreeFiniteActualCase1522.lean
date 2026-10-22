/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1522 : Family 10 := level10.get ⟨363,by decide⟩
def sourceMap1522 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1522 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1522_checked : acceptsGraphIso
    (source (graph core1522) (root 10) 0 2) DegreeTwoThreeSpectrum2796.graph sourceMap1522=true := by decide +kernel
theorem fusedMap1522_checked : acceptsGraphIso
    (fused (graph core1522) (root 10) 0 2) DegreeTwoThreeSpectrum2808.graph fusedMap1522=true := by decide +kernel
theorem certified1522 : Certified (graph core1522) (root 10) 0 2 :=
  of_native_maps core1522 DegreeTwoThreeSpectrum2796.graph DegreeTwoThreeSpectrum2808.graph
    sourceMap1522 fusedMap1522 sourceMap1522_checked fusedMap1522_checked
    DegreeTwoThreeFiniteComparisons.comparison1522
#print axioms sourceMap1522_checked
#print axioms fusedMap1522_checked
#print axioms certified1522
def sourceMap1522swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1522swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1522swap_checked : acceptsGraphIso
    (source (graph core1522) (root 10) 2 0) DegreeTwoThreeSpectrum2796.graph sourceMap1522swap=true := by decide +kernel
theorem fusedMap1522swap_checked : acceptsGraphIso
    (fused (graph core1522) (root 10) 2 0) DegreeTwoThreeSpectrum2808.graph fusedMap1522swap=true := by decide +kernel
theorem certified1522swap : Certified (graph core1522) (root 10) 2 0 :=
  of_native_maps core1522 DegreeTwoThreeSpectrum2796.graph DegreeTwoThreeSpectrum2808.graph
    sourceMap1522swap fusedMap1522swap sourceMap1522swap_checked fusedMap1522swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1522
#print axioms sourceMap1522swap_checked
#print axioms fusedMap1522swap_checked
#print axioms certified1522swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
