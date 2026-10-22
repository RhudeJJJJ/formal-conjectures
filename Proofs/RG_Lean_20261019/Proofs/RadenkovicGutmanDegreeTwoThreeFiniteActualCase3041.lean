/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3041 : Family 10 := level10.get ⟨1664,by decide⟩
def sourceMap3041 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3041 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3041_checked : acceptsGraphIso
    (source (graph core3041) (root 10) 0 4) DegreeTwoThreeSpectrum7229.graph sourceMap3041=true := by decide +kernel
theorem fusedMap3041_checked : acceptsGraphIso
    (fused (graph core3041) (root 10) 0 4) DegreeTwoThreeSpectrum6281.graph fusedMap3041=true := by decide +kernel
theorem certified3041 : Certified (graph core3041) (root 10) 0 4 :=
  of_native_maps core3041 DegreeTwoThreeSpectrum7229.graph DegreeTwoThreeSpectrum6281.graph
    sourceMap3041 fusedMap3041 sourceMap3041_checked fusedMap3041_checked
    DegreeTwoThreeFiniteComparisons.comparison3041
#print axioms sourceMap3041_checked
#print axioms fusedMap3041_checked
#print axioms certified3041
def sourceMap3041swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3041swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3041swap_checked : acceptsGraphIso
    (source (graph core3041) (root 10) 4 0) DegreeTwoThreeSpectrum7229.graph sourceMap3041swap=true := by decide +kernel
theorem fusedMap3041swap_checked : acceptsGraphIso
    (fused (graph core3041) (root 10) 4 0) DegreeTwoThreeSpectrum6281.graph fusedMap3041swap=true := by decide +kernel
theorem certified3041swap : Certified (graph core3041) (root 10) 4 0 :=
  of_native_maps core3041 DegreeTwoThreeSpectrum7229.graph DegreeTwoThreeSpectrum6281.graph
    sourceMap3041swap fusedMap3041swap sourceMap3041swap_checked fusedMap3041swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3041
#print axioms sourceMap3041swap_checked
#print axioms fusedMap3041swap_checked
#print axioms certified3041swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
