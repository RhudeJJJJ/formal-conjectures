/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3975 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap3975 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3975 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3975_checked : acceptsGraphIso
    (source (graph core3975) (root 7) 1 5) DegreeTwoThreeSpectrum4335.graph sourceMap3975=true := by decide +kernel
theorem fusedMap3975_checked : acceptsGraphIso
    (fused (graph core3975) (root 7) 1 5) DegreeTwoThreeSpectrum3941.graph fusedMap3975=true := by decide +kernel
theorem certified3975 : Certified (graph core3975) (root 7) 1 5 :=
  of_native_maps core3975 DegreeTwoThreeSpectrum4335.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap3975 fusedMap3975 sourceMap3975_checked fusedMap3975_checked
    DegreeTwoThreeFiniteComparisons.comparison3975
#print axioms sourceMap3975_checked
#print axioms fusedMap3975_checked
#print axioms certified3975
def sourceMap3975swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3975swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3975swap_checked : acceptsGraphIso
    (source (graph core3975) (root 7) 5 1) DegreeTwoThreeSpectrum4335.graph sourceMap3975swap=true := by decide +kernel
theorem fusedMap3975swap_checked : acceptsGraphIso
    (fused (graph core3975) (root 7) 5 1) DegreeTwoThreeSpectrum3941.graph fusedMap3975swap=true := by decide +kernel
theorem certified3975swap : Certified (graph core3975) (root 7) 5 1 :=
  of_native_maps core3975 DegreeTwoThreeSpectrum4335.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap3975swap fusedMap3975swap sourceMap3975swap_checked fusedMap3975swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3975
#print axioms sourceMap3975swap_checked
#print axioms fusedMap3975swap_checked
#print axioms certified3975swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
