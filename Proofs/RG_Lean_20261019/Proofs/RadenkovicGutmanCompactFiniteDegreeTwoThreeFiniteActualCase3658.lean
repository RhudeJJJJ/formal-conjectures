/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3658 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap3658 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3658 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3658_checked : acceptsGraphIso
    (source (graph core3658) (root 6) 0 7) DegreeTwoThreeSpectrum4064.graph sourceMap3658=true := by decide +kernel
theorem fusedMap3658_checked : acceptsGraphIso
    (fused (graph core3658) (root 6) 0 7) DegreeTwoThreeSpectrum4067.graph fusedMap3658=true := by decide +kernel
theorem certified3658 : Certified (graph core3658) (root 6) 0 7 :=
  of_native_maps core3658 DegreeTwoThreeSpectrum4064.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap3658 fusedMap3658 sourceMap3658_checked fusedMap3658_checked
    DegreeTwoThreeFiniteComparisons.comparison3658
#print axioms sourceMap3658_checked
#print axioms fusedMap3658_checked
#print axioms certified3658
def sourceMap3658swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3658swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3658swap_checked : acceptsGraphIso
    (source (graph core3658) (root 6) 7 0) DegreeTwoThreeSpectrum4064.graph sourceMap3658swap=true := by decide +kernel
theorem fusedMap3658swap_checked : acceptsGraphIso
    (fused (graph core3658) (root 6) 7 0) DegreeTwoThreeSpectrum4067.graph fusedMap3658swap=true := by decide +kernel
theorem certified3658swap : Certified (graph core3658) (root 6) 7 0 :=
  of_native_maps core3658 DegreeTwoThreeSpectrum4064.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap3658swap fusedMap3658swap sourceMap3658swap_checked fusedMap3658swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3658
#print axioms sourceMap3658swap_checked
#print axioms fusedMap3658swap_checked
#print axioms certified3658swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
