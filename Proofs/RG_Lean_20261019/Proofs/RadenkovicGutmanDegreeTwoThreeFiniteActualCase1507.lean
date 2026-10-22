/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1507 : Family 10 := level10.get ⟨317,by decide⟩
def sourceMap1507 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1507 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1507_checked : acceptsGraphIso
    (source (graph core1507) (root 10) 0 2) DegreeTwoThreeSpectrum2720.graph sourceMap1507=true := by decide +kernel
theorem fusedMap1507_checked : acceptsGraphIso
    (fused (graph core1507) (root 10) 0 2) DegreeTwoThreeSpectrum2722.graph fusedMap1507=true := by decide +kernel
theorem certified1507 : Certified (graph core1507) (root 10) 0 2 :=
  of_native_maps core1507 DegreeTwoThreeSpectrum2720.graph DegreeTwoThreeSpectrum2722.graph
    sourceMap1507 fusedMap1507 sourceMap1507_checked fusedMap1507_checked
    DegreeTwoThreeFiniteComparisons.comparison1507
#print axioms sourceMap1507_checked
#print axioms fusedMap1507_checked
#print axioms certified1507
def sourceMap1507swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1507swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1507swap_checked : acceptsGraphIso
    (source (graph core1507) (root 10) 2 0) DegreeTwoThreeSpectrum2720.graph sourceMap1507swap=true := by decide +kernel
theorem fusedMap1507swap_checked : acceptsGraphIso
    (fused (graph core1507) (root 10) 2 0) DegreeTwoThreeSpectrum2722.graph fusedMap1507swap=true := by decide +kernel
theorem certified1507swap : Certified (graph core1507) (root 10) 2 0 :=
  of_native_maps core1507 DegreeTwoThreeSpectrum2720.graph DegreeTwoThreeSpectrum2722.graph
    sourceMap1507swap fusedMap1507swap sourceMap1507swap_checked fusedMap1507swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1507
#print axioms sourceMap1507swap_checked
#print axioms fusedMap1507swap_checked
#print axioms certified1507swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
