/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0501 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0501 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (sourceLabel 7 0 0 v)
def fusedMap0501 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,5,0,1,2,3,4,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0501_checked : acceptsGraphIso
    (source (graph core0501) (root 7) 0 0) DegreeOneSmallSpectrum117.graph sourceMap0501=true := by decide +kernel
theorem fusedMap0501_checked : acceptsGraphIso
    (fused (graph core0501) (root 7) 0 0) DegreeOneSmallSpectrum079.graph fusedMap0501=true := by decide +kernel
theorem certified0501 : Certified (graph core0501) (root 7) 0 0 :=
  of_native_maps core0501 DegreeOneSmallSpectrum117.graph DegreeOneSmallSpectrum079.graph
    sourceMap0501 fusedMap0501 sourceMap0501_checked fusedMap0501_checked
    DegreeOneSmallComparisons.comparison0501
#print axioms sourceMap0501_checked
#print axioms fusedMap0501_checked
#print axioms certified0501
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
