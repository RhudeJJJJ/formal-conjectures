/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3773 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3773 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap3773 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap3773_checked : acceptsGraphIso
    (source (graph core3773) (root 5) 1 4) DegreeOneSmallSpectrum1089.graph sourceMap3773=true := by decide +kernel
theorem fusedMap3773_checked : acceptsGraphIso
    (fused (graph core3773) (root 5) 1 4) DegreeOneSmallSpectrum871.graph fusedMap3773=true := by decide +kernel
theorem certified3773 : Certified (graph core3773) (root 5) 1 4 :=
  of_native_maps core3773 DegreeOneSmallSpectrum1089.graph DegreeOneSmallSpectrum871.graph
    sourceMap3773 fusedMap3773 sourceMap3773_checked fusedMap3773_checked
    DegreeTwoThreeFiniteComparisons.comparison3773
#print axioms sourceMap3773_checked
#print axioms fusedMap3773_checked
#print axioms certified3773
def sourceMap3773swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap3773swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap3773swap_checked : acceptsGraphIso
    (source (graph core3773) (root 5) 4 1) DegreeOneSmallSpectrum1089.graph sourceMap3773swap=true := by decide +kernel
theorem fusedMap3773swap_checked : acceptsGraphIso
    (fused (graph core3773) (root 5) 4 1) DegreeOneSmallSpectrum871.graph fusedMap3773swap=true := by decide +kernel
theorem certified3773swap : Certified (graph core3773) (root 5) 4 1 :=
  of_native_maps core3773 DegreeOneSmallSpectrum1089.graph DegreeOneSmallSpectrum871.graph
    sourceMap3773swap fusedMap3773swap sourceMap3773swap_checked fusedMap3773swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3773
#print axioms sourceMap3773swap_checked
#print axioms fusedMap3773swap_checked
#print axioms certified3773swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
