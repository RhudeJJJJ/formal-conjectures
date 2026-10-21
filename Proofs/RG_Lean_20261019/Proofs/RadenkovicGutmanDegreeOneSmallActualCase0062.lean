/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0062 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0062 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (sourceLabel 3 0 7 v)
def fusedMap0062 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 0 7 v)
theorem sourceMap0062_checked : acceptsGraphIso
    (source (graph core0062) (root 3) 0 7) DegreeOneSmallSpectrum858.graph sourceMap0062=true := by decide +kernel
theorem fusedMap0062_checked : acceptsGraphIso
    (fused (graph core0062) (root 3) 0 7) DegreeOneSmallSpectrum861.graph fusedMap0062=true := by decide +kernel
theorem certified0062 : Certified (graph core0062) (root 3) 0 7 :=
  of_native_maps core0062 DegreeOneSmallSpectrum858.graph DegreeOneSmallSpectrum861.graph
    sourceMap0062 fusedMap0062 sourceMap0062_checked fusedMap0062_checked
    DegreeOneSmallComparisons.comparison0062
#print axioms sourceMap0062_checked
#print axioms fusedMap0062_checked
#print axioms certified0062
def sourceMap0062swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,11,12,6] (sourceLabel 3 7 0 v)
def fusedMap0062swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 7 0 v)
theorem sourceMap0062swap_checked : acceptsGraphIso
    (source (graph core0062) (root 3) 7 0) DegreeOneSmallSpectrum858.graph sourceMap0062swap=true := by decide +kernel
theorem fusedMap0062swap_checked : acceptsGraphIso
    (fused (graph core0062) (root 3) 7 0) DegreeOneSmallSpectrum861.graph fusedMap0062swap=true := by decide +kernel
theorem certified0062swap : Certified (graph core0062) (root 3) 7 0 :=
  of_native_maps core0062 DegreeOneSmallSpectrum858.graph DegreeOneSmallSpectrum861.graph
    sourceMap0062swap fusedMap0062swap sourceMap0062swap_checked fusedMap0062swap_checked
    DegreeOneSmallComparisons.comparison0062
#print axioms sourceMap0062swap_checked
#print axioms fusedMap0062swap_checked
#print axioms certified0062swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
