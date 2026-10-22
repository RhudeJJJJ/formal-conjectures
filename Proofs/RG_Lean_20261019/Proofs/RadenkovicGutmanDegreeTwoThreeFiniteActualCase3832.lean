/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3832 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap3832 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,8,6,7,1,2,3,4,5] (sourceLabel 8 1 4 v)
def fusedMap3832 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3832_checked : acceptsGraphIso
    (source (graph core3832) (root 8) 1 4) DegreeTwoThreeSpectrum4159.graph sourceMap3832=true := by decide +kernel
theorem fusedMap3832_checked : acceptsGraphIso
    (fused (graph core3832) (root 8) 1 4) DegreeTwoThreeSpectrum3885.graph fusedMap3832=true := by decide +kernel
theorem certified3832 : Certified (graph core3832) (root 8) 1 4 :=
  of_native_maps core3832 DegreeTwoThreeSpectrum4159.graph DegreeTwoThreeSpectrum3885.graph
    sourceMap3832 fusedMap3832 sourceMap3832_checked fusedMap3832_checked
    DegreeTwoThreeFiniteComparisons.comparison3832
#print axioms sourceMap3832_checked
#print axioms fusedMap3832_checked
#print axioms certified3832
def sourceMap3832swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,8,1,2,3,4,5,6,7] (sourceLabel 8 4 1 v)
def fusedMap3832swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3832swap_checked : acceptsGraphIso
    (source (graph core3832) (root 8) 4 1) DegreeTwoThreeSpectrum4159.graph sourceMap3832swap=true := by decide +kernel
theorem fusedMap3832swap_checked : acceptsGraphIso
    (fused (graph core3832) (root 8) 4 1) DegreeTwoThreeSpectrum3885.graph fusedMap3832swap=true := by decide +kernel
theorem certified3832swap : Certified (graph core3832) (root 8) 4 1 :=
  of_native_maps core3832 DegreeTwoThreeSpectrum4159.graph DegreeTwoThreeSpectrum3885.graph
    sourceMap3832swap fusedMap3832swap sourceMap3832swap_checked fusedMap3832swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3832
#print axioms sourceMap3832swap_checked
#print axioms fusedMap3832swap_checked
#print axioms certified3832swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
