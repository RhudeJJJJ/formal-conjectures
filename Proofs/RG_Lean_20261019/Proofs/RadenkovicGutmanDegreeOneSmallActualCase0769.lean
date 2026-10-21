/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0769 : Family 8 := level8.get ⟨9,by decide⟩
def sourceMap0769 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0769 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0769_checked : acceptsGraphIso
    (source (graph core0769) (root 8) 0 2) DegreeOneSmallSpectrum877.graph sourceMap0769=true := by decide +kernel
theorem fusedMap0769_checked : acceptsGraphIso
    (fused (graph core0769) (root 8) 0 2) DegreeOneSmallSpectrum879.graph fusedMap0769=true := by decide +kernel
theorem certified0769 : Certified (graph core0769) (root 8) 0 2 :=
  of_native_maps core0769 DegreeOneSmallSpectrum877.graph DegreeOneSmallSpectrum879.graph
    sourceMap0769 fusedMap0769 sourceMap0769_checked fusedMap0769_checked
    DegreeOneSmallComparisons.comparison0769
#print axioms sourceMap0769_checked
#print axioms fusedMap0769_checked
#print axioms certified0769
def sourceMap0769swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0769swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0769swap_checked : acceptsGraphIso
    (source (graph core0769) (root 8) 2 0) DegreeOneSmallSpectrum877.graph sourceMap0769swap=true := by decide +kernel
theorem fusedMap0769swap_checked : acceptsGraphIso
    (fused (graph core0769) (root 8) 2 0) DegreeOneSmallSpectrum879.graph fusedMap0769swap=true := by decide +kernel
theorem certified0769swap : Certified (graph core0769) (root 8) 2 0 :=
  of_native_maps core0769 DegreeOneSmallSpectrum877.graph DegreeOneSmallSpectrum879.graph
    sourceMap0769swap fusedMap0769swap sourceMap0769swap_checked fusedMap0769swap_checked
    DegreeOneSmallComparisons.comparison0769
#print axioms sourceMap0769swap_checked
#print axioms fusedMap0769swap_checked
#print axioms certified0769swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
