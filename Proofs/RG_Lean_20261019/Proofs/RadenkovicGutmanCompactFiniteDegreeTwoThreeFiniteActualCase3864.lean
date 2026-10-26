/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3864 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap3864 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3864 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3864_checked : acceptsGraphIso
    (source (graph core3864) (root 8) 1 4) DegreeTwoThreeSpectrum4374.graph sourceMap3864=true := by decide +kernel
theorem fusedMap3864_checked : acceptsGraphIso
    (fused (graph core3864) (root 8) 1 4) DegreeTwoThreeSpectrum3959.graph fusedMap3864=true := by decide +kernel
theorem certified3864 : Certified (graph core3864) (root 8) 1 4 :=
  of_native_maps core3864 DegreeTwoThreeSpectrum4374.graph DegreeTwoThreeSpectrum3959.graph
    sourceMap3864 fusedMap3864 sourceMap3864_checked fusedMap3864_checked
    DegreeTwoThreeFiniteComparisons.comparison3864
#print axioms sourceMap3864_checked
#print axioms fusedMap3864_checked
#print axioms certified3864
def sourceMap3864swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3864swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3864swap_checked : acceptsGraphIso
    (source (graph core3864) (root 8) 4 1) DegreeTwoThreeSpectrum4374.graph sourceMap3864swap=true := by decide +kernel
theorem fusedMap3864swap_checked : acceptsGraphIso
    (fused (graph core3864) (root 8) 4 1) DegreeTwoThreeSpectrum3959.graph fusedMap3864swap=true := by decide +kernel
theorem certified3864swap : Certified (graph core3864) (root 8) 4 1 :=
  of_native_maps core3864 DegreeTwoThreeSpectrum4374.graph DegreeTwoThreeSpectrum3959.graph
    sourceMap3864swap fusedMap3864swap sourceMap3864swap_checked fusedMap3864swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3864
#print axioms sourceMap3864swap_checked
#print axioms fusedMap3864swap_checked
#print axioms certified3864swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
