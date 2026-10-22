/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3772 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3772 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap3772 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap3772_checked : acceptsGraphIso
    (source (graph core3772) (root 5) 1 4) DegreeOneSmallSpectrum1010.graph sourceMap3772=true := by decide +kernel
theorem fusedMap3772_checked : acceptsGraphIso
    (fused (graph core3772) (root 5) 1 4) DegreeOneSmallSpectrum863.graph fusedMap3772=true := by decide +kernel
theorem certified3772 : Certified (graph core3772) (root 5) 1 4 :=
  of_native_maps core3772 DegreeOneSmallSpectrum1010.graph DegreeOneSmallSpectrum863.graph
    sourceMap3772 fusedMap3772 sourceMap3772_checked fusedMap3772_checked
    DegreeTwoThreeFiniteComparisons.comparison3772
#print axioms sourceMap3772_checked
#print axioms fusedMap3772_checked
#print axioms certified3772
def sourceMap3772swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,6,7] (sourceLabel 5 4 1 v)
def fusedMap3772swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap3772swap_checked : acceptsGraphIso
    (source (graph core3772) (root 5) 4 1) DegreeOneSmallSpectrum1010.graph sourceMap3772swap=true := by decide +kernel
theorem fusedMap3772swap_checked : acceptsGraphIso
    (fused (graph core3772) (root 5) 4 1) DegreeOneSmallSpectrum863.graph fusedMap3772swap=true := by decide +kernel
theorem certified3772swap : Certified (graph core3772) (root 5) 4 1 :=
  of_native_maps core3772 DegreeOneSmallSpectrum1010.graph DegreeOneSmallSpectrum863.graph
    sourceMap3772swap fusedMap3772swap sourceMap3772swap_checked fusedMap3772swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3772
#print axioms sourceMap3772swap_checked
#print axioms fusedMap3772swap_checked
#print axioms certified3772swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
