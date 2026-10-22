/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3111 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap3111 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3111 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3111_checked : acceptsGraphIso
    (source (graph core3111) (root 7) 0 5) DegreeTwoThreeSpectrum2590.graph sourceMap3111=true := by decide +kernel
theorem fusedMap3111_checked : acceptsGraphIso
    (fused (graph core3111) (root 7) 0 5) DegreeTwoThreeSpectrum2330.graph fusedMap3111=true := by decide +kernel
theorem certified3111 : Certified (graph core3111) (root 7) 0 5 :=
  of_native_maps core3111 DegreeTwoThreeSpectrum2590.graph DegreeTwoThreeSpectrum2330.graph
    sourceMap3111 fusedMap3111 sourceMap3111_checked fusedMap3111_checked
    DegreeTwoThreeFiniteComparisons.comparison3111
#print axioms sourceMap3111_checked
#print axioms fusedMap3111_checked
#print axioms certified3111
def sourceMap3111swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3111swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3111swap_checked : acceptsGraphIso
    (source (graph core3111) (root 7) 5 0) DegreeTwoThreeSpectrum2590.graph sourceMap3111swap=true := by decide +kernel
theorem fusedMap3111swap_checked : acceptsGraphIso
    (fused (graph core3111) (root 7) 5 0) DegreeTwoThreeSpectrum2330.graph fusedMap3111swap=true := by decide +kernel
theorem certified3111swap : Certified (graph core3111) (root 7) 5 0 :=
  of_native_maps core3111 DegreeTwoThreeSpectrum2590.graph DegreeTwoThreeSpectrum2330.graph
    sourceMap3111swap fusedMap3111swap sourceMap3111swap_checked fusedMap3111swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3111
#print axioms sourceMap3111swap_checked
#print axioms fusedMap3111swap_checked
#print axioms certified3111swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
