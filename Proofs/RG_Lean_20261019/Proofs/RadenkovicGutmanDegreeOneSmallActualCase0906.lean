/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0906 : Family 8 := level8.get ⟨57,by decide⟩
def sourceMap0906 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0906 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0906_checked : acceptsGraphIso
    (source (graph core0906) (root 8) 1 1) DegreeOneSmallSpectrum1333.graph sourceMap0906=true := by decide +kernel
theorem fusedMap0906_checked : acceptsGraphIso
    (fused (graph core0906) (root 8) 1 1) DegreeOneSmallSpectrum916.graph fusedMap0906=true := by decide +kernel
theorem certified0906 : Certified (graph core0906) (root 8) 1 1 :=
  of_native_maps core0906 DegreeOneSmallSpectrum1333.graph DegreeOneSmallSpectrum916.graph
    sourceMap0906 fusedMap0906 sourceMap0906_checked fusedMap0906_checked
    DegreeOneSmallComparisons.comparison0906
#print axioms sourceMap0906_checked
#print axioms fusedMap0906_checked
#print axioms certified0906
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
