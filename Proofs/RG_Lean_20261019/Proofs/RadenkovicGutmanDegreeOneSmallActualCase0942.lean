/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0942 : Family 8 := level8.get ⟨71,by decide⟩
def sourceMap0942 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0942 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0942_checked : acceptsGraphIso
    (source (graph core0942) (root 8) 1 1) DegreeOneSmallSpectrum1341.graph sourceMap0942=true := by decide +kernel
theorem fusedMap0942_checked : acceptsGraphIso
    (fused (graph core0942) (root 8) 1 1) DegreeOneSmallSpectrum946.graph fusedMap0942=true := by decide +kernel
theorem certified0942 : Certified (graph core0942) (root 8) 1 1 :=
  of_native_maps core0942 DegreeOneSmallSpectrum1341.graph DegreeOneSmallSpectrum946.graph
    sourceMap0942 fusedMap0942 sourceMap0942_checked fusedMap0942_checked
    DegreeOneSmallComparisons.comparison0942
#print axioms sourceMap0942_checked
#print axioms fusedMap0942_checked
#print axioms certified0942
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
