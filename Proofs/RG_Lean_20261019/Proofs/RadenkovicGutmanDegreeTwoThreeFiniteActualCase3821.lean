/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3821 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap3821 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3821 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3821_checked : acceptsGraphIso
    (source (graph core3821) (root 7) 1 4) DegreeTwoThreeSpectrum3532.graph sourceMap3821=true := by decide +kernel
theorem fusedMap3821_checked : acceptsGraphIso
    (fused (graph core3821) (root 7) 1 4) DegreeTwoThreeSpectrum2734.graph fusedMap3821=true := by decide +kernel
theorem certified3821 : Certified (graph core3821) (root 7) 1 4 :=
  of_native_maps core3821 DegreeTwoThreeSpectrum3532.graph DegreeTwoThreeSpectrum2734.graph
    sourceMap3821 fusedMap3821 sourceMap3821_checked fusedMap3821_checked
    DegreeTwoThreeFiniteComparisons.comparison3821
#print axioms sourceMap3821_checked
#print axioms fusedMap3821_checked
#print axioms certified3821
def sourceMap3821swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3821swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3821swap_checked : acceptsGraphIso
    (source (graph core3821) (root 7) 4 1) DegreeTwoThreeSpectrum3532.graph sourceMap3821swap=true := by decide +kernel
theorem fusedMap3821swap_checked : acceptsGraphIso
    (fused (graph core3821) (root 7) 4 1) DegreeTwoThreeSpectrum2734.graph fusedMap3821swap=true := by decide +kernel
theorem certified3821swap : Certified (graph core3821) (root 7) 4 1 :=
  of_native_maps core3821 DegreeTwoThreeSpectrum3532.graph DegreeTwoThreeSpectrum2734.graph
    sourceMap3821swap fusedMap3821swap sourceMap3821swap_checked fusedMap3821swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3821
#print axioms sourceMap3821swap_checked
#print axioms fusedMap3821swap_checked
#print axioms certified3821swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
