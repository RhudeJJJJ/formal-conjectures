/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0902 : Family 8 := level8.get ⟨55,by decide⟩
def sourceMap0902 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0902 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0902_checked : acceptsGraphIso
    (source (graph core0902) (root 8) 1 1) DegreeOneSmallSpectrum1324.graph sourceMap0902=true := by decide +kernel
theorem fusedMap0902_checked : acceptsGraphIso
    (fused (graph core0902) (root 8) 1 1) DegreeOneSmallSpectrum911.graph fusedMap0902=true := by decide +kernel
theorem certified0902 : Certified (graph core0902) (root 8) 1 1 :=
  of_native_maps core0902 DegreeOneSmallSpectrum1324.graph DegreeOneSmallSpectrum911.graph
    sourceMap0902 fusedMap0902 sourceMap0902_checked fusedMap0902_checked
    DegreeOneSmallComparisons.comparison0902
#print axioms sourceMap0902_checked
#print axioms fusedMap0902_checked
#print axioms certified0902
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
