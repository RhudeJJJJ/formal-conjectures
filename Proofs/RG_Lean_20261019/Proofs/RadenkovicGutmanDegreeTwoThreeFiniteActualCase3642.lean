/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3642 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3642 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (sourceLabel 5 0 7 v)
def fusedMap3642 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 0 7 v)
theorem sourceMap3642_checked : acceptsGraphIso
    (source (graph core3642) (root 5) 0 7) DegreeTwoThreeSpectrum2361.graph sourceMap3642=true := by decide +kernel
theorem fusedMap3642_checked : acceptsGraphIso
    (fused (graph core3642) (root 5) 0 7) DegreeTwoThreeSpectrum2365.graph fusedMap3642=true := by decide +kernel
theorem certified3642 : Certified (graph core3642) (root 5) 0 7 :=
  of_native_maps core3642 DegreeTwoThreeSpectrum2361.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap3642 fusedMap3642 sourceMap3642_checked fusedMap3642_checked
    DegreeTwoThreeFiniteComparisons.comparison3642
#print axioms sourceMap3642_checked
#print axioms fusedMap3642_checked
#print axioms certified3642
def sourceMap3642swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,14,8] (sourceLabel 5 7 0 v)
def fusedMap3642swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 7 0 v)
theorem sourceMap3642swap_checked : acceptsGraphIso
    (source (graph core3642) (root 5) 7 0) DegreeTwoThreeSpectrum2361.graph sourceMap3642swap=true := by decide +kernel
theorem fusedMap3642swap_checked : acceptsGraphIso
    (fused (graph core3642) (root 5) 7 0) DegreeTwoThreeSpectrum2365.graph fusedMap3642swap=true := by decide +kernel
theorem certified3642swap : Certified (graph core3642) (root 5) 7 0 :=
  of_native_maps core3642 DegreeTwoThreeSpectrum2361.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap3642swap fusedMap3642swap sourceMap3642swap_checked fusedMap3642swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3642
#print axioms sourceMap3642swap_checked
#print axioms fusedMap3642swap_checked
#print axioms certified3642swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
