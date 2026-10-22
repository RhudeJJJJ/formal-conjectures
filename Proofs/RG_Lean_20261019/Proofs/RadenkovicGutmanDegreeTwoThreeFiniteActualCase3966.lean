/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3966 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap3966 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3966 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3966_checked : acceptsGraphIso
    (source (graph core3966) (root 7) 1 5) DegreeTwoThreeSpectrum4619.graph sourceMap3966=true := by decide +kernel
theorem fusedMap3966_checked : acceptsGraphIso
    (fused (graph core3966) (root 7) 1 5) DegreeTwoThreeSpectrum4096.graph fusedMap3966=true := by decide +kernel
theorem certified3966 : Certified (graph core3966) (root 7) 1 5 :=
  of_native_maps core3966 DegreeTwoThreeSpectrum4619.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap3966 fusedMap3966 sourceMap3966_checked fusedMap3966_checked
    DegreeTwoThreeFiniteComparisons.comparison3966
#print axioms sourceMap3966_checked
#print axioms fusedMap3966_checked
#print axioms certified3966
def sourceMap3966swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3966swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3966swap_checked : acceptsGraphIso
    (source (graph core3966) (root 7) 5 1) DegreeTwoThreeSpectrum4619.graph sourceMap3966swap=true := by decide +kernel
theorem fusedMap3966swap_checked : acceptsGraphIso
    (fused (graph core3966) (root 7) 5 1) DegreeTwoThreeSpectrum4096.graph fusedMap3966swap=true := by decide +kernel
theorem certified3966swap : Certified (graph core3966) (root 7) 5 1 :=
  of_native_maps core3966 DegreeTwoThreeSpectrum4619.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap3966swap fusedMap3966swap sourceMap3966swap_checked fusedMap3966swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3966
#print axioms sourceMap3966swap_checked
#print axioms fusedMap3966swap_checked
#print axioms certified3966swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
