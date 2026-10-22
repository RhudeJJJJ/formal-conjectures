/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3714 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap3714 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3714 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3714_checked : acceptsGraphIso
    (source (graph core3714) (root 6) 0 8) DegreeTwoThreeSpectrum5083.graph sourceMap3714=true := by decide +kernel
theorem fusedMap3714_checked : acceptsGraphIso
    (fused (graph core3714) (root 6) 0 8) DegreeTwoThreeSpectrum5087.graph fusedMap3714=true := by decide +kernel
theorem certified3714 : Certified (graph core3714) (root 6) 0 8 :=
  of_native_maps core3714 DegreeTwoThreeSpectrum5083.graph DegreeTwoThreeSpectrum5087.graph
    sourceMap3714 fusedMap3714 sourceMap3714_checked fusedMap3714_checked
    DegreeTwoThreeFiniteComparisons.comparison3714
#print axioms sourceMap3714_checked
#print axioms fusedMap3714_checked
#print axioms certified3714
def sourceMap3714swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,16,9] (sourceLabel 6 8 0 v)
def fusedMap3714swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3714swap_checked : acceptsGraphIso
    (source (graph core3714) (root 6) 8 0) DegreeTwoThreeSpectrum5083.graph sourceMap3714swap=true := by decide +kernel
theorem fusedMap3714swap_checked : acceptsGraphIso
    (fused (graph core3714) (root 6) 8 0) DegreeTwoThreeSpectrum5087.graph fusedMap3714swap=true := by decide +kernel
theorem certified3714swap : Certified (graph core3714) (root 6) 8 0 :=
  of_native_maps core3714 DegreeTwoThreeSpectrum5083.graph DegreeTwoThreeSpectrum5087.graph
    sourceMap3714swap fusedMap3714swap sourceMap3714swap_checked fusedMap3714swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3714
#print axioms sourceMap3714swap_checked
#print axioms fusedMap3714swap_checked
#print axioms certified3714swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
