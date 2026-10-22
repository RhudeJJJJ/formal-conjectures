/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3639 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3639 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (sourceLabel 4 0 7 v)
def fusedMap3639 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 0 7 v)
theorem sourceMap3639_checked : acceptsGraphIso
    (source (graph core3639) (root 4) 0 7) DegreeTwoThreeSpectrum1807.graph sourceMap3639=true := by decide +kernel
theorem fusedMap3639_checked : acceptsGraphIso
    (fused (graph core3639) (root 4) 0 7) DegreeTwoThreeSpectrum1716.graph fusedMap3639=true := by decide +kernel
theorem certified3639 : Certified (graph core3639) (root 4) 0 7 :=
  of_native_maps core3639 DegreeTwoThreeSpectrum1807.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap3639 fusedMap3639 sourceMap3639_checked fusedMap3639_checked
    DegreeTwoThreeFiniteComparisons.comparison3639
#print axioms sourceMap3639_checked
#print axioms fusedMap3639_checked
#print axioms certified3639
def sourceMap3639swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 1) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,9,10,11,12,13,8] (sourceLabel 4 7 0 v)
def fusedMap3639swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 7 0 v)
theorem sourceMap3639swap_checked : acceptsGraphIso
    (source (graph core3639) (root 4) 7 0) DegreeTwoThreeSpectrum1807.graph sourceMap3639swap=true := by decide +kernel
theorem fusedMap3639swap_checked : acceptsGraphIso
    (fused (graph core3639) (root 4) 7 0) DegreeTwoThreeSpectrum1716.graph fusedMap3639swap=true := by decide +kernel
theorem certified3639swap : Certified (graph core3639) (root 4) 7 0 :=
  of_native_maps core3639 DegreeTwoThreeSpectrum1807.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap3639swap fusedMap3639swap sourceMap3639swap_checked fusedMap3639swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3639
#print axioms sourceMap3639swap_checked
#print axioms fusedMap3639swap_checked
#print axioms certified3639swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
