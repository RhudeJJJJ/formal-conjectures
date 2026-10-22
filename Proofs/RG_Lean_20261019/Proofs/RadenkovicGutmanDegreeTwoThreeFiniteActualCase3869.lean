/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3869 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap3869 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3869 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3869_checked : acceptsGraphIso
    (source (graph core3869) (root 8) 1 4) DegreeTwoThreeSpectrum4452.graph sourceMap3869=true := by decide +kernel
theorem fusedMap3869_checked : acceptsGraphIso
    (fused (graph core3869) (root 8) 1 4) DegreeTwoThreeSpectrum4002.graph fusedMap3869=true := by decide +kernel
theorem certified3869 : Certified (graph core3869) (root 8) 1 4 :=
  of_native_maps core3869 DegreeTwoThreeSpectrum4452.graph DegreeTwoThreeSpectrum4002.graph
    sourceMap3869 fusedMap3869 sourceMap3869_checked fusedMap3869_checked
    DegreeTwoThreeFiniteComparisons.comparison3869
#print axioms sourceMap3869_checked
#print axioms fusedMap3869_checked
#print axioms certified3869
def sourceMap3869swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3869swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3869swap_checked : acceptsGraphIso
    (source (graph core3869) (root 8) 4 1) DegreeTwoThreeSpectrum4452.graph sourceMap3869swap=true := by decide +kernel
theorem fusedMap3869swap_checked : acceptsGraphIso
    (fused (graph core3869) (root 8) 4 1) DegreeTwoThreeSpectrum4002.graph fusedMap3869swap=true := by decide +kernel
theorem certified3869swap : Certified (graph core3869) (root 8) 4 1 :=
  of_native_maps core3869 DegreeTwoThreeSpectrum4452.graph DegreeTwoThreeSpectrum4002.graph
    sourceMap3869swap fusedMap3869swap sourceMap3869swap_checked fusedMap3869swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3869
#print axioms sourceMap3869swap_checked
#print axioms fusedMap3869swap_checked
#print axioms certified3869swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
