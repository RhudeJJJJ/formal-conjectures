/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0938 : Family 8 := level8.get ⟨70,by decide⟩
def sourceMap0938 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0938 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0938_checked : acceptsGraphIso
    (source (graph core0938) (root 8) 1 1) DegreeOneSmallSpectrum1340.graph sourceMap0938=true := by decide +kernel
theorem fusedMap0938_checked : acceptsGraphIso
    (fused (graph core0938) (root 8) 1 1) DegreeOneSmallSpectrum945.graph fusedMap0938=true := by decide +kernel
theorem certified0938 : Certified (graph core0938) (root 8) 1 1 :=
  of_native_maps core0938 DegreeOneSmallSpectrum1340.graph DegreeOneSmallSpectrum945.graph
    sourceMap0938 fusedMap0938 sourceMap0938_checked fusedMap0938_checked
    DegreeOneSmallComparisons.comparison0938
#print axioms sourceMap0938_checked
#print axioms fusedMap0938_checked
#print axioms certified0938
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
