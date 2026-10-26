/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3649 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap3649 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3649 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3649_checked : acceptsGraphIso
    (source (graph core3649) (root 6) 0 7) DegreeTwoThreeSpectrum4098.graph sourceMap3649=true := by decide +kernel
theorem fusedMap3649_checked : acceptsGraphIso
    (fused (graph core3649) (root 6) 0 7) DegreeTwoThreeSpectrum3872.graph fusedMap3649=true := by decide +kernel
theorem certified3649 : Certified (graph core3649) (root 6) 0 7 :=
  of_native_maps core3649 DegreeTwoThreeSpectrum4098.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap3649 fusedMap3649 sourceMap3649_checked fusedMap3649_checked
    DegreeTwoThreeFiniteComparisons.comparison3649
#print axioms sourceMap3649_checked
#print axioms fusedMap3649_checked
#print axioms certified3649
def sourceMap3649swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3649swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3649swap_checked : acceptsGraphIso
    (source (graph core3649) (root 6) 7 0) DegreeTwoThreeSpectrum4098.graph sourceMap3649swap=true := by decide +kernel
theorem fusedMap3649swap_checked : acceptsGraphIso
    (fused (graph core3649) (root 6) 7 0) DegreeTwoThreeSpectrum3872.graph fusedMap3649swap=true := by decide +kernel
theorem certified3649swap : Certified (graph core3649) (root 6) 7 0 :=
  of_native_maps core3649 DegreeTwoThreeSpectrum4098.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap3649swap fusedMap3649swap sourceMap3649swap_checked fusedMap3649swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3649
#print axioms sourceMap3649swap_checked
#print axioms fusedMap3649swap_checked
#print axioms certified3649swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
