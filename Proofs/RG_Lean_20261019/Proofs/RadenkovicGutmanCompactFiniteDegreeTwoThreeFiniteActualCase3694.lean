/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3694 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap3694 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3694 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3694_checked : acceptsGraphIso
    (source (graph core3694) (root 7) 0 7) DegreeTwoThreeSpectrum5546.graph sourceMap3694=true := by decide +kernel
theorem fusedMap3694_checked : acceptsGraphIso
    (fused (graph core3694) (root 7) 0 7) DegreeTwoThreeSpectrum5549.graph fusedMap3694=true := by decide +kernel
theorem certified3694 : Certified (graph core3694) (root 7) 0 7 :=
  of_native_maps core3694 DegreeTwoThreeSpectrum5546.graph DegreeTwoThreeSpectrum5549.graph
    sourceMap3694 fusedMap3694 sourceMap3694_checked fusedMap3694_checked
    DegreeTwoThreeFiniteComparisons.comparison3694
#print axioms sourceMap3694_checked
#print axioms fusedMap3694_checked
#print axioms certified3694
def sourceMap3694swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3694swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3694swap_checked : acceptsGraphIso
    (source (graph core3694) (root 7) 7 0) DegreeTwoThreeSpectrum5546.graph sourceMap3694swap=true := by decide +kernel
theorem fusedMap3694swap_checked : acceptsGraphIso
    (fused (graph core3694) (root 7) 7 0) DegreeTwoThreeSpectrum5549.graph fusedMap3694swap=true := by decide +kernel
theorem certified3694swap : Certified (graph core3694) (root 7) 7 0 :=
  of_native_maps core3694 DegreeTwoThreeSpectrum5546.graph DegreeTwoThreeSpectrum5549.graph
    sourceMap3694swap fusedMap3694swap sourceMap3694swap_checked fusedMap3694swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3694
#print axioms sourceMap3694swap_checked
#print axioms fusedMap3694swap_checked
#print axioms certified3694swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
