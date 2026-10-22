/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3973 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap3973 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3973 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3973_checked : acceptsGraphIso
    (source (graph core3973) (root 7) 1 5) DegreeTwoThreeSpectrum4294.graph sourceMap3973=true := by decide +kernel
theorem fusedMap3973_checked : acceptsGraphIso
    (fused (graph core3973) (root 7) 1 5) DegreeTwoThreeSpectrum3923.graph fusedMap3973=true := by decide +kernel
theorem certified3973 : Certified (graph core3973) (root 7) 1 5 :=
  of_native_maps core3973 DegreeTwoThreeSpectrum4294.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap3973 fusedMap3973 sourceMap3973_checked fusedMap3973_checked
    DegreeTwoThreeFiniteComparisons.comparison3973
#print axioms sourceMap3973_checked
#print axioms fusedMap3973_checked
#print axioms certified3973
def sourceMap3973swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3973swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3973swap_checked : acceptsGraphIso
    (source (graph core3973) (root 7) 5 1) DegreeTwoThreeSpectrum4294.graph sourceMap3973swap=true := by decide +kernel
theorem fusedMap3973swap_checked : acceptsGraphIso
    (fused (graph core3973) (root 7) 5 1) DegreeTwoThreeSpectrum3923.graph fusedMap3973swap=true := by decide +kernel
theorem certified3973swap : Certified (graph core3973) (root 7) 5 1 :=
  of_native_maps core3973 DegreeTwoThreeSpectrum4294.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap3973swap fusedMap3973swap sourceMap3973swap_checked fusedMap3973swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3973
#print axioms sourceMap3973swap_checked
#print axioms fusedMap3973swap_checked
#print axioms certified3973swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
