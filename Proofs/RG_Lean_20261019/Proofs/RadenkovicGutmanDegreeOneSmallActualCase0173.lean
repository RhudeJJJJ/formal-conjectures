/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0173 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0173 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,9,6,7,8] (sourceLabel 5 0 2 v)
def fusedMap0173 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0173_checked : acceptsGraphIso
    (source (graph core0173) (root 5) 0 2) DegreeOneSmallSpectrum079.graph sourceMap0173=true := by decide +kernel
theorem fusedMap0173_checked : acceptsGraphIso
    (fused (graph core0173) (root 5) 0 2) DegreeOneSmallSpectrum080.graph fusedMap0173=true := by decide +kernel
theorem certified0173 : Certified (graph core0173) (root 5) 0 2 :=
  of_native_maps core0173 DegreeOneSmallSpectrum079.graph DegreeOneSmallSpectrum080.graph
    sourceMap0173 fusedMap0173 sourceMap0173_checked fusedMap0173_checked
    DegreeOneSmallComparisons.comparison0173
#print axioms sourceMap0173_checked
#print axioms fusedMap0173_checked
#print axioms certified0173
def sourceMap0173swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 5 2 0 v)
def fusedMap0173swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0173swap_checked : acceptsGraphIso
    (source (graph core0173) (root 5) 2 0) DegreeOneSmallSpectrum079.graph sourceMap0173swap=true := by decide +kernel
theorem fusedMap0173swap_checked : acceptsGraphIso
    (fused (graph core0173) (root 5) 2 0) DegreeOneSmallSpectrum080.graph fusedMap0173swap=true := by decide +kernel
theorem certified0173swap : Certified (graph core0173) (root 5) 2 0 :=
  of_native_maps core0173 DegreeOneSmallSpectrum079.graph DegreeOneSmallSpectrum080.graph
    sourceMap0173swap fusedMap0173swap sourceMap0173swap_checked fusedMap0173swap_checked
    DegreeOneSmallComparisons.comparison0173
#print axioms sourceMap0173swap_checked
#print axioms fusedMap0173swap_checked
#print axioms certified0173swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
