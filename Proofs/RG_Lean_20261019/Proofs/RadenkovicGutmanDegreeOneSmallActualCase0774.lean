/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0774 : Family 8 := level8.get ⟨10,by decide⟩
def sourceMap0774 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0774 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0774_checked : acceptsGraphIso
    (source (graph core0774) (root 8) 1 1) DegreeOneSmallSpectrum1231.graph sourceMap0774=true := by decide +kernel
theorem fusedMap0774_checked : acceptsGraphIso
    (fused (graph core0774) (root 8) 1 1) DegreeOneSmallSpectrum887.graph fusedMap0774=true := by decide +kernel
theorem certified0774 : Certified (graph core0774) (root 8) 1 1 :=
  of_native_maps core0774 DegreeOneSmallSpectrum1231.graph DegreeOneSmallSpectrum887.graph
    sourceMap0774 fusedMap0774 sourceMap0774_checked fusedMap0774_checked
    DegreeOneSmallComparisons.comparison0774
#print axioms sourceMap0774_checked
#print axioms fusedMap0774_checked
#print axioms certified0774
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
