/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3925 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3925 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,7,5,6,0,8,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap3925 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap3925_checked : acceptsGraphIso
    (source (graph core3925) (root 4) 1 5) DegreeOneSmallSpectrum947.graph sourceMap3925=true := by decide +kernel
theorem fusedMap3925_checked : acceptsGraphIso
    (fused (graph core3925) (root 4) 1 5) DegreeOneSmallSpectrum858.graph fusedMap3925=true := by decide +kernel
theorem certified3925 : Certified (graph core3925) (root 4) 1 5 :=
  of_native_maps core3925 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum858.graph
    sourceMap3925 fusedMap3925 sourceMap3925_checked fusedMap3925_checked
    DegreeTwoThreeFiniteComparisons.comparison3925
#print axioms sourceMap3925_checked
#print axioms fusedMap3925_checked
#print axioms certified3925
def sourceMap3925swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,7,0,8,9,10,11,12,5,6] (sourceLabel 4 5 1 v)
def fusedMap3925swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap3925swap_checked : acceptsGraphIso
    (source (graph core3925) (root 4) 5 1) DegreeOneSmallSpectrum947.graph sourceMap3925swap=true := by decide +kernel
theorem fusedMap3925swap_checked : acceptsGraphIso
    (fused (graph core3925) (root 4) 5 1) DegreeOneSmallSpectrum858.graph fusedMap3925swap=true := by decide +kernel
theorem certified3925swap : Certified (graph core3925) (root 4) 5 1 :=
  of_native_maps core3925 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum858.graph
    sourceMap3925swap fusedMap3925swap sourceMap3925swap_checked fusedMap3925swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3925
#print axioms sourceMap3925swap_checked
#print axioms fusedMap3925swap_checked
#print axioms certified3925swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
