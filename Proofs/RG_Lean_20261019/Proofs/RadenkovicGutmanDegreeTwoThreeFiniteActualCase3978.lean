/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3978 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap3978 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3978 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3978_checked : acceptsGraphIso
    (source (graph core3978) (root 7) 1 5) DegreeTwoThreeSpectrum4420.graph sourceMap3978=true := by decide +kernel
theorem fusedMap3978_checked : acceptsGraphIso
    (fused (graph core3978) (root 7) 1 5) DegreeTwoThreeSpectrum3987.graph fusedMap3978=true := by decide +kernel
theorem certified3978 : Certified (graph core3978) (root 7) 1 5 :=
  of_native_maps core3978 DegreeTwoThreeSpectrum4420.graph DegreeTwoThreeSpectrum3987.graph
    sourceMap3978 fusedMap3978 sourceMap3978_checked fusedMap3978_checked
    DegreeTwoThreeFiniteComparisons.comparison3978
#print axioms sourceMap3978_checked
#print axioms fusedMap3978_checked
#print axioms certified3978
def sourceMap3978swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3978swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3978swap_checked : acceptsGraphIso
    (source (graph core3978) (root 7) 5 1) DegreeTwoThreeSpectrum4420.graph sourceMap3978swap=true := by decide +kernel
theorem fusedMap3978swap_checked : acceptsGraphIso
    (fused (graph core3978) (root 7) 5 1) DegreeTwoThreeSpectrum3987.graph fusedMap3978swap=true := by decide +kernel
theorem certified3978swap : Certified (graph core3978) (root 7) 5 1 :=
  of_native_maps core3978 DegreeTwoThreeSpectrum4420.graph DegreeTwoThreeSpectrum3987.graph
    sourceMap3978swap fusedMap3978swap sourceMap3978swap_checked fusedMap3978swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3978
#print axioms sourceMap3978swap_checked
#print axioms fusedMap3978swap_checked
#print axioms certified3978swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
