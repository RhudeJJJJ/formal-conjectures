/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0383 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0383 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap0383 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0383_checked : acceptsGraphIso
    (source (graph core0383) (root 6) 2 2) DegreeOneSmallSpectrum1461.graph sourceMap0383=true := by decide +kernel
theorem fusedMap0383_checked : acceptsGraphIso
    (fused (graph core0383) (root 6) 2 2) DegreeOneSmallSpectrum956.graph fusedMap0383=true := by decide +kernel
theorem certified0383 : Certified (graph core0383) (root 6) 2 2 :=
  of_native_maps core0383 DegreeOneSmallSpectrum1461.graph DegreeOneSmallSpectrum956.graph
    sourceMap0383 fusedMap0383 sourceMap0383_checked fusedMap0383_checked
    DegreeOneSmallComparisons.comparison0383
#print axioms sourceMap0383_checked
#print axioms fusedMap0383_checked
#print axioms certified0383
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
