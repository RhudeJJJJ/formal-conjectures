/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0537 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0537 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0537 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0537_checked : acceptsGraphIso
    (source (graph core0537) (root 7) 0 0) DegreeOneSmallSpectrum129.graph sourceMap0537=true := by decide +kernel
theorem fusedMap0537_checked : acceptsGraphIso
    (fused (graph core0537) (root 7) 0 0) DegreeOneSmallSpectrum088.graph fusedMap0537=true := by decide +kernel
theorem certified0537 : Certified (graph core0537) (root 7) 0 0 :=
  of_native_maps core0537 DegreeOneSmallSpectrum129.graph DegreeOneSmallSpectrum088.graph
    sourceMap0537 fusedMap0537 sourceMap0537_checked fusedMap0537_checked
    DegreeOneSmallComparisons.comparison0537
#print axioms sourceMap0537_checked
#print axioms fusedMap0537_checked
#print axioms certified0537
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
