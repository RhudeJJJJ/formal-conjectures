/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3355 : Family 9 := level9.get ⟨383,by decide⟩
def sourceMap3355 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3355 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3355_checked : acceptsGraphIso
    (source (graph core3355) (root 9) 0 5) DegreeTwoThreeSpectrum6325.graph sourceMap3355=true := by decide +kernel
theorem fusedMap3355_checked : acceptsGraphIso
    (fused (graph core3355) (root 9) 0 5) DegreeTwoThreeSpectrum5283.graph fusedMap3355=true := by decide +kernel
theorem certified3355 : Certified (graph core3355) (root 9) 0 5 :=
  of_native_maps core3355 DegreeTwoThreeSpectrum6325.graph DegreeTwoThreeSpectrum5283.graph
    sourceMap3355 fusedMap3355 sourceMap3355_checked fusedMap3355_checked
    DegreeTwoThreeFiniteComparisons.comparison3355
#print axioms sourceMap3355_checked
#print axioms fusedMap3355_checked
#print axioms certified3355
def sourceMap3355swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3355swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3355swap_checked : acceptsGraphIso
    (source (graph core3355) (root 9) 5 0) DegreeTwoThreeSpectrum6325.graph sourceMap3355swap=true := by decide +kernel
theorem fusedMap3355swap_checked : acceptsGraphIso
    (fused (graph core3355) (root 9) 5 0) DegreeTwoThreeSpectrum5283.graph fusedMap3355swap=true := by decide +kernel
theorem certified3355swap : Certified (graph core3355) (root 9) 5 0 :=
  of_native_maps core3355 DegreeTwoThreeSpectrum6325.graph DegreeTwoThreeSpectrum5283.graph
    sourceMap3355swap fusedMap3355swap sourceMap3355swap_checked fusedMap3355swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3355
#print axioms sourceMap3355swap_checked
#print axioms fusedMap3355swap_checked
#print axioms certified3355swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
