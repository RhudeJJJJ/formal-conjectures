/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3134 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap3134 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3134 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3134_checked : acceptsGraphIso
    (source (graph core3134) (root 7) 0 5) DegreeTwoThreeSpectrum2732.graph sourceMap3134=true := by decide +kernel
theorem fusedMap3134_checked : acceptsGraphIso
    (fused (graph core3134) (root 7) 0 5) DegreeTwoThreeSpectrum2734.graph fusedMap3134=true := by decide +kernel
theorem certified3134 : Certified (graph core3134) (root 7) 0 5 :=
  of_native_maps core3134 DegreeTwoThreeSpectrum2732.graph DegreeTwoThreeSpectrum2734.graph
    sourceMap3134 fusedMap3134 sourceMap3134_checked fusedMap3134_checked
    DegreeTwoThreeFiniteComparisons.comparison3134
#print axioms sourceMap3134_checked
#print axioms fusedMap3134_checked
#print axioms certified3134
def sourceMap3134swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3134swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3134swap_checked : acceptsGraphIso
    (source (graph core3134) (root 7) 5 0) DegreeTwoThreeSpectrum2732.graph sourceMap3134swap=true := by decide +kernel
theorem fusedMap3134swap_checked : acceptsGraphIso
    (fused (graph core3134) (root 7) 5 0) DegreeTwoThreeSpectrum2734.graph fusedMap3134swap=true := by decide +kernel
theorem certified3134swap : Certified (graph core3134) (root 7) 5 0 :=
  of_native_maps core3134 DegreeTwoThreeSpectrum2732.graph DegreeTwoThreeSpectrum2734.graph
    sourceMap3134swap fusedMap3134swap sourceMap3134swap_checked fusedMap3134swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3134
#print axioms sourceMap3134swap_checked
#print axioms fusedMap3134swap_checked
#print axioms certified3134swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
