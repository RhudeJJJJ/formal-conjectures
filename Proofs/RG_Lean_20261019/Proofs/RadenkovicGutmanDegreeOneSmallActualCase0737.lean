/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0737 : Family 8 := level8.get ⟨0,by decide⟩
def sourceMap0737 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 8 0 2 v)
def fusedMap0737 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 8 0 2 v)
theorem sourceMap0737_checked : acceptsGraphIso
    (source (graph core0737) (root 8) 0 2) DegreeOneSmallSpectrum858.graph sourceMap0737=true := by decide +kernel
theorem fusedMap0737_checked : acceptsGraphIso
    (fused (graph core0737) (root 8) 0 2) DegreeOneSmallSpectrum861.graph fusedMap0737=true := by decide +kernel
theorem certified0737 : Certified (graph core0737) (root 8) 0 2 :=
  of_native_maps core0737 DegreeOneSmallSpectrum858.graph DegreeOneSmallSpectrum861.graph
    sourceMap0737 fusedMap0737 sourceMap0737_checked fusedMap0737_checked
    DegreeOneSmallComparisons.comparison0737
#print axioms sourceMap0737_checked
#print axioms fusedMap0737_checked
#print axioms certified0737
def sourceMap0737swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 2 0 v)
def fusedMap0737swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 8 2 0 v)
theorem sourceMap0737swap_checked : acceptsGraphIso
    (source (graph core0737) (root 8) 2 0) DegreeOneSmallSpectrum858.graph sourceMap0737swap=true := by decide +kernel
theorem fusedMap0737swap_checked : acceptsGraphIso
    (fused (graph core0737) (root 8) 2 0) DegreeOneSmallSpectrum861.graph fusedMap0737swap=true := by decide +kernel
theorem certified0737swap : Certified (graph core0737) (root 8) 2 0 :=
  of_native_maps core0737 DegreeOneSmallSpectrum858.graph DegreeOneSmallSpectrum861.graph
    sourceMap0737swap fusedMap0737swap sourceMap0737swap_checked fusedMap0737swap_checked
    DegreeOneSmallComparisons.comparison0737
#print axioms sourceMap0737swap_checked
#print axioms fusedMap0737swap_checked
#print axioms certified0737swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
