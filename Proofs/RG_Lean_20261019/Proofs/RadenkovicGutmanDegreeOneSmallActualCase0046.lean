/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0046 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0046 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,7,8,1,2,3,4,5,6] (sourceLabel 2 2 2 v)
def fusedMap0046 : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 2 2 v)
theorem sourceMap0046_checked : acceptsGraphIso
    (source (graph core0046) (root 2) 2 2) DegreeOneSmallSpectrum061.graph sourceMap0046=true := by decide +kernel
theorem fusedMap0046_checked : acceptsGraphIso
    (fused (graph core0046) (root 2) 2 2) DegreeOneSmallSpectrum037.graph fusedMap0046=true := by decide +kernel
theorem certified0046 : Certified (graph core0046) (root 2) 2 2 :=
  of_native_maps core0046 DegreeOneSmallSpectrum061.graph DegreeOneSmallSpectrum037.graph
    sourceMap0046 fusedMap0046 sourceMap0046_checked fusedMap0046_checked
    DegreeOneSmallComparisons.comparison0046
#print axioms sourceMap0046_checked
#print axioms fusedMap0046_checked
#print axioms certified0046
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
