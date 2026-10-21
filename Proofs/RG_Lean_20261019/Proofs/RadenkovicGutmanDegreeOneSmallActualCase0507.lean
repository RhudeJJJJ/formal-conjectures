/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0507 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0507 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0507 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0507_checked : acceptsGraphIso
    (source (graph core0507) (root 7) 0 0) DegreeOneSmallSpectrum124.graph sourceMap0507=true := by decide +kernel
theorem fusedMap0507_checked : acceptsGraphIso
    (fused (graph core0507) (root 7) 0 0) DegreeOneSmallSpectrum081.graph fusedMap0507=true := by decide +kernel
theorem certified0507 : Certified (graph core0507) (root 7) 0 0 :=
  of_native_maps core0507 DegreeOneSmallSpectrum124.graph DegreeOneSmallSpectrum081.graph
    sourceMap0507 fusedMap0507 sourceMap0507_checked fusedMap0507_checked
    DegreeOneSmallComparisons.comparison0507
#print axioms sourceMap0507_checked
#print axioms fusedMap0507_checked
#print axioms certified0507
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
