/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3986 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap3986 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3986 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3986_checked : acceptsGraphIso
    (source (graph core3986) (root 7) 1 5) DegreeTwoThreeSpectrum4694.graph sourceMap3986=true := by decide +kernel
theorem fusedMap3986_checked : acceptsGraphIso
    (fused (graph core3986) (root 7) 1 5) DegreeTwoThreeSpectrum4207.graph fusedMap3986=true := by decide +kernel
theorem certified3986 : Certified (graph core3986) (root 7) 1 5 :=
  of_native_maps core3986 DegreeTwoThreeSpectrum4694.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap3986 fusedMap3986 sourceMap3986_checked fusedMap3986_checked
    DegreeTwoThreeFiniteComparisons.comparison3986
#print axioms sourceMap3986_checked
#print axioms fusedMap3986_checked
#print axioms certified3986
def sourceMap3986swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,12,13,14,15,10,11] (sourceLabel 7 5 1 v)
def fusedMap3986swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3986swap_checked : acceptsGraphIso
    (source (graph core3986) (root 7) 5 1) DegreeTwoThreeSpectrum4694.graph sourceMap3986swap=true := by decide +kernel
theorem fusedMap3986swap_checked : acceptsGraphIso
    (fused (graph core3986) (root 7) 5 1) DegreeTwoThreeSpectrum4207.graph fusedMap3986swap=true := by decide +kernel
theorem certified3986swap : Certified (graph core3986) (root 7) 5 1 :=
  of_native_maps core3986 DegreeTwoThreeSpectrum4694.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap3986swap fusedMap3986swap sourceMap3986swap_checked fusedMap3986swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3986
#print axioms sourceMap3986swap_checked
#print axioms fusedMap3986swap_checked
#print axioms certified3986swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
