/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3798 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap3798 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3798 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3798_checked : acceptsGraphIso
    (source (graph core3798) (root 7) 1 4) DegreeTwoThreeSpectrum2586.graph sourceMap3798=true := by decide +kernel
theorem fusedMap3798_checked : acceptsGraphIso
    (fused (graph core3798) (root 7) 1 4) DegreeTwoThreeSpectrum2330.graph fusedMap3798=true := by decide +kernel
theorem certified3798 : Certified (graph core3798) (root 7) 1 4 :=
  of_native_maps core3798 DegreeTwoThreeSpectrum2586.graph DegreeTwoThreeSpectrum2330.graph
    sourceMap3798 fusedMap3798 sourceMap3798_checked fusedMap3798_checked
    DegreeTwoThreeFiniteComparisons.comparison3798
#print axioms sourceMap3798_checked
#print axioms fusedMap3798_checked
#print axioms certified3798
def sourceMap3798swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3798swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3798swap_checked : acceptsGraphIso
    (source (graph core3798) (root 7) 4 1) DegreeTwoThreeSpectrum2586.graph sourceMap3798swap=true := by decide +kernel
theorem fusedMap3798swap_checked : acceptsGraphIso
    (fused (graph core3798) (root 7) 4 1) DegreeTwoThreeSpectrum2330.graph fusedMap3798swap=true := by decide +kernel
theorem certified3798swap : Certified (graph core3798) (root 7) 4 1 :=
  of_native_maps core3798 DegreeTwoThreeSpectrum2586.graph DegreeTwoThreeSpectrum2330.graph
    sourceMap3798swap fusedMap3798swap sourceMap3798swap_checked fusedMap3798swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3798
#print axioms sourceMap3798swap_checked
#print axioms fusedMap3798swap_checked
#print axioms certified3798swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
