/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0807 : Family 8 := level8.get ⟨21,by decide⟩
def sourceMap0807 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0807 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0807_checked : acceptsGraphIso
    (source (graph core0807) (root 8) 0 0) DegreeOneSmallSpectrum195.graph sourceMap0807=true := by decide +kernel
theorem fusedMap0807_checked : acceptsGraphIso
    (fused (graph core0807) (root 8) 0 0) DegreeOneSmallSpectrum225.graph fusedMap0807=true := by decide +kernel
theorem certified0807 : Certified (graph core0807) (root 8) 0 0 :=
  of_native_maps core0807 DegreeOneSmallSpectrum195.graph DegreeOneSmallSpectrum225.graph
    sourceMap0807 fusedMap0807 sourceMap0807_checked fusedMap0807_checked
    DegreeOneSmallComparisons.comparison0807
#print axioms sourceMap0807_checked
#print axioms fusedMap0807_checked
#print axioms certified0807
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
