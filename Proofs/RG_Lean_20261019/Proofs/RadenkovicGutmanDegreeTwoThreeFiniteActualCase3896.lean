/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3896 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap3896 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3896 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3896_checked : acceptsGraphIso
    (source (graph core3896) (root 8) 1 4) DegreeTwoThreeSpectrum4713.graph sourceMap3896=true := by decide +kernel
theorem fusedMap3896_checked : acceptsGraphIso
    (fused (graph core3896) (root 8) 1 4) DegreeTwoThreeSpectrum4239.graph fusedMap3896=true := by decide +kernel
theorem certified3896 : Certified (graph core3896) (root 8) 1 4 :=
  of_native_maps core3896 DegreeTwoThreeSpectrum4713.graph DegreeTwoThreeSpectrum4239.graph
    sourceMap3896 fusedMap3896 sourceMap3896_checked fusedMap3896_checked
    DegreeTwoThreeFiniteComparisons.comparison3896
#print axioms sourceMap3896_checked
#print axioms fusedMap3896_checked
#print axioms certified3896
def sourceMap3896swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3896swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3896swap_checked : acceptsGraphIso
    (source (graph core3896) (root 8) 4 1) DegreeTwoThreeSpectrum4713.graph sourceMap3896swap=true := by decide +kernel
theorem fusedMap3896swap_checked : acceptsGraphIso
    (fused (graph core3896) (root 8) 4 1) DegreeTwoThreeSpectrum4239.graph fusedMap3896swap=true := by decide +kernel
theorem certified3896swap : Certified (graph core3896) (root 8) 4 1 :=
  of_native_maps core3896 DegreeTwoThreeSpectrum4713.graph DegreeTwoThreeSpectrum4239.graph
    sourceMap3896swap fusedMap3896swap sourceMap3896swap_checked fusedMap3896swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3896
#print axioms sourceMap3896swap_checked
#print axioms fusedMap3896swap_checked
#print axioms certified3896swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
