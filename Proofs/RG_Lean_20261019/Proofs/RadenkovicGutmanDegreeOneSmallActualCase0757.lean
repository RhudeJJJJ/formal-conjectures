/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0757 : Family 8 := level8.get ⟨5,by decide⟩
def sourceMap0757 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 8 0 2 v)
def fusedMap0757 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0757_checked : acceptsGraphIso
    (source (graph core0757) (root 8) 0 2) DegreeOneSmallSpectrum966.graph sourceMap0757=true := by decide +kernel
theorem fusedMap0757_checked : acceptsGraphIso
    (fused (graph core0757) (root 8) 0 2) DegreeOneSmallSpectrum860.graph fusedMap0757=true := by decide +kernel
theorem certified0757 : Certified (graph core0757) (root 8) 0 2 :=
  of_native_maps core0757 DegreeOneSmallSpectrum966.graph DegreeOneSmallSpectrum860.graph
    sourceMap0757 fusedMap0757 sourceMap0757_checked fusedMap0757_checked
    DegreeOneSmallComparisons.comparison0757
#print axioms sourceMap0757_checked
#print axioms fusedMap0757_checked
#print axioms certified0757
def sourceMap0757swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 2 0 v)
def fusedMap0757swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0757swap_checked : acceptsGraphIso
    (source (graph core0757) (root 8) 2 0) DegreeOneSmallSpectrum966.graph sourceMap0757swap=true := by decide +kernel
theorem fusedMap0757swap_checked : acceptsGraphIso
    (fused (graph core0757) (root 8) 2 0) DegreeOneSmallSpectrum860.graph fusedMap0757swap=true := by decide +kernel
theorem certified0757swap : Certified (graph core0757) (root 8) 2 0 :=
  of_native_maps core0757 DegreeOneSmallSpectrum966.graph DegreeOneSmallSpectrum860.graph
    sourceMap0757swap fusedMap0757swap sourceMap0757swap_checked fusedMap0757swap_checked
    DegreeOneSmallComparisons.comparison0757
#print axioms sourceMap0757swap_checked
#print axioms fusedMap0757swap_checked
#print axioms certified0757swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
