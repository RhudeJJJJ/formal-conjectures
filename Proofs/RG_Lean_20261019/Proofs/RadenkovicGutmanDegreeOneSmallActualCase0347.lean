/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0347 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0347 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0347 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0347_checked : acceptsGraphIso
    (source (graph core0347) (root 6) 2 2) DegreeOneSmallSpectrum1340.graph sourceMap0347=true := by decide +kernel
theorem fusedMap0347_checked : acceptsGraphIso
    (fused (graph core0347) (root 6) 2 2) DegreeOneSmallSpectrum915.graph fusedMap0347=true := by decide +kernel
theorem certified0347 : Certified (graph core0347) (root 6) 2 2 :=
  of_native_maps core0347 DegreeOneSmallSpectrum1340.graph DegreeOneSmallSpectrum915.graph
    sourceMap0347 fusedMap0347 sourceMap0347_checked fusedMap0347_checked
    DegreeOneSmallComparisons.comparison0347
#print axioms sourceMap0347_checked
#print axioms fusedMap0347_checked
#print axioms certified0347
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
