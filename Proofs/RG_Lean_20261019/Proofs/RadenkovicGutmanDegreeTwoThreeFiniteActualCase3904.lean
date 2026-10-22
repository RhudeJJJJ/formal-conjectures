/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3904 : Family 8 := level8.get ⟨222,by decide⟩
def sourceMap3904 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3904 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3904_checked : acceptsGraphIso
    (source (graph core3904) (root 8) 1 4) DegreeTwoThreeSpectrum4758.graph sourceMap3904=true := by decide +kernel
theorem fusedMap3904_checked : acceptsGraphIso
    (fused (graph core3904) (root 8) 1 4) DegreeTwoThreeSpectrum4330.graph fusedMap3904=true := by decide +kernel
theorem certified3904 : Certified (graph core3904) (root 8) 1 4 :=
  of_native_maps core3904 DegreeTwoThreeSpectrum4758.graph DegreeTwoThreeSpectrum4330.graph
    sourceMap3904 fusedMap3904 sourceMap3904_checked fusedMap3904_checked
    DegreeTwoThreeFiniteComparisons.comparison3904
#print axioms sourceMap3904_checked
#print axioms fusedMap3904_checked
#print axioms certified3904
def sourceMap3904swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3904swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3904swap_checked : acceptsGraphIso
    (source (graph core3904) (root 8) 4 1) DegreeTwoThreeSpectrum4758.graph sourceMap3904swap=true := by decide +kernel
theorem fusedMap3904swap_checked : acceptsGraphIso
    (fused (graph core3904) (root 8) 4 1) DegreeTwoThreeSpectrum4330.graph fusedMap3904swap=true := by decide +kernel
theorem certified3904swap : Certified (graph core3904) (root 8) 4 1 :=
  of_native_maps core3904 DegreeTwoThreeSpectrum4758.graph DegreeTwoThreeSpectrum4330.graph
    sourceMap3904swap fusedMap3904swap sourceMap3904swap_checked fusedMap3904swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3904
#print axioms sourceMap3904swap_checked
#print axioms fusedMap3904swap_checked
#print axioms certified3904swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
