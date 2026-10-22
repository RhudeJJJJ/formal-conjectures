/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3849 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap3849 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3849 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3849_checked : acceptsGraphIso
    (source (graph core3849) (root 8) 1 4) DegreeTwoThreeSpectrum4654.graph sourceMap3849=true := by decide +kernel
theorem fusedMap3849_checked : acceptsGraphIso
    (fused (graph core3849) (root 8) 1 4) DegreeTwoThreeSpectrum4136.graph fusedMap3849=true := by decide +kernel
theorem certified3849 : Certified (graph core3849) (root 8) 1 4 :=
  of_native_maps core3849 DegreeTwoThreeSpectrum4654.graph DegreeTwoThreeSpectrum4136.graph
    sourceMap3849 fusedMap3849 sourceMap3849_checked fusedMap3849_checked
    DegreeTwoThreeFiniteComparisons.comparison3849
#print axioms sourceMap3849_checked
#print axioms fusedMap3849_checked
#print axioms certified3849
def sourceMap3849swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3849swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3849swap_checked : acceptsGraphIso
    (source (graph core3849) (root 8) 4 1) DegreeTwoThreeSpectrum4654.graph sourceMap3849swap=true := by decide +kernel
theorem fusedMap3849swap_checked : acceptsGraphIso
    (fused (graph core3849) (root 8) 4 1) DegreeTwoThreeSpectrum4136.graph fusedMap3849swap=true := by decide +kernel
theorem certified3849swap : Certified (graph core3849) (root 8) 4 1 :=
  of_native_maps core3849 DegreeTwoThreeSpectrum4654.graph DegreeTwoThreeSpectrum4136.graph
    sourceMap3849swap fusedMap3849swap sourceMap3849swap_checked fusedMap3849swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3849
#print axioms sourceMap3849swap_checked
#print axioms fusedMap3849swap_checked
#print axioms certified3849swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
