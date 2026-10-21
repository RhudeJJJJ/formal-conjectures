/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0703 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0703 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0703 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0703_checked : acceptsGraphIso
    (source (graph core0703) (root 7) 1 1) DegreeOneSmallSpectrum694.graph sourceMap0703=true := by decide +kernel
theorem fusedMap0703_checked : acceptsGraphIso
    (fused (graph core0703) (root 7) 1 1) DegreeOneSmallSpectrum429.graph fusedMap0703=true := by decide +kernel
theorem certified0703 : Certified (graph core0703) (root 7) 1 1 :=
  of_native_maps core0703 DegreeOneSmallSpectrum694.graph DegreeOneSmallSpectrum429.graph
    sourceMap0703 fusedMap0703 sourceMap0703_checked fusedMap0703_checked
    DegreeOneSmallComparisons.comparison0703
#print axioms sourceMap0703_checked
#print axioms fusedMap0703_checked
#print axioms certified0703
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
