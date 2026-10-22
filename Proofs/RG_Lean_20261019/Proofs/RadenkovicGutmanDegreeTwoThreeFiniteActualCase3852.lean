/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3852 : Family 8 := level8.get ⟨92,by decide⟩
def sourceMap3852 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10] (sourceLabel 8 1 4 v)
def fusedMap3852 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3852_checked : acceptsGraphIso
    (source (graph core3852) (root 8) 1 4) DegreeTwoThreeSpectrum4663.graph sourceMap3852=true := by decide +kernel
theorem fusedMap3852_checked : acceptsGraphIso
    (fused (graph core3852) (root 8) 1 4) DegreeTwoThreeSpectrum4157.graph fusedMap3852=true := by decide +kernel
theorem certified3852 : Certified (graph core3852) (root 8) 1 4 :=
  of_native_maps core3852 DegreeTwoThreeSpectrum4663.graph DegreeTwoThreeSpectrum4157.graph
    sourceMap3852 fusedMap3852 sourceMap3852_checked fusedMap3852_checked
    DegreeTwoThreeFiniteComparisons.comparison3852
#print axioms sourceMap3852_checked
#print axioms fusedMap3852_checked
#print axioms certified3852
def sourceMap3852swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,6,7,8,9,10,14,15] (sourceLabel 8 4 1 v)
def fusedMap3852swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3852swap_checked : acceptsGraphIso
    (source (graph core3852) (root 8) 4 1) DegreeTwoThreeSpectrum4663.graph sourceMap3852swap=true := by decide +kernel
theorem fusedMap3852swap_checked : acceptsGraphIso
    (fused (graph core3852) (root 8) 4 1) DegreeTwoThreeSpectrum4157.graph fusedMap3852swap=true := by decide +kernel
theorem certified3852swap : Certified (graph core3852) (root 8) 4 1 :=
  of_native_maps core3852 DegreeTwoThreeSpectrum4663.graph DegreeTwoThreeSpectrum4157.graph
    sourceMap3852swap fusedMap3852swap sourceMap3852swap_checked fusedMap3852swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3852
#print axioms sourceMap3852swap_checked
#print axioms fusedMap3852swap_checked
#print axioms certified3852swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
