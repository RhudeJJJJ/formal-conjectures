/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3008 : Family 10 := level10.get ⟨1585,by decide⟩
def sourceMap3008 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3008 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3008_checked : acceptsGraphIso
    (source (graph core3008) (root 10) 0 4) DegreeTwoThreeSpectrum7123.graph sourceMap3008=true := by decide +kernel
theorem fusedMap3008_checked : acceptsGraphIso
    (fused (graph core3008) (root 10) 0 4) DegreeTwoThreeSpectrum6074.graph fusedMap3008=true := by decide +kernel
theorem certified3008 : Certified (graph core3008) (root 10) 0 4 :=
  of_native_maps core3008 DegreeTwoThreeSpectrum7123.graph DegreeTwoThreeSpectrum6074.graph
    sourceMap3008 fusedMap3008 sourceMap3008_checked fusedMap3008_checked
    DegreeTwoThreeFiniteComparisons.comparison3008
#print axioms sourceMap3008_checked
#print axioms fusedMap3008_checked
#print axioms certified3008
def sourceMap3008swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3008swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3008swap_checked : acceptsGraphIso
    (source (graph core3008) (root 10) 4 0) DegreeTwoThreeSpectrum7123.graph sourceMap3008swap=true := by decide +kernel
theorem fusedMap3008swap_checked : acceptsGraphIso
    (fused (graph core3008) (root 10) 4 0) DegreeTwoThreeSpectrum6074.graph fusedMap3008swap=true := by decide +kernel
theorem certified3008swap : Certified (graph core3008) (root 10) 4 0 :=
  of_native_maps core3008 DegreeTwoThreeSpectrum7123.graph DegreeTwoThreeSpectrum6074.graph
    sourceMap3008swap fusedMap3008swap sourceMap3008swap_checked fusedMap3008swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3008
#print axioms sourceMap3008swap_checked
#print axioms fusedMap3008swap_checked
#print axioms certified3008swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
