/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0039 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0039 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (sourceLabel 2 1 1 v)
def fusedMap0039 : (Vertices 2 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (fusedLabel 2 1 1 v)
theorem sourceMap0039_checked : acceptsGraphIso
    (source (graph core0039) (root 2) 1 1) DegreeOneSmallSpectrum015.graph sourceMap0039=true := by decide +kernel
theorem fusedMap0039_checked : acceptsGraphIso
    (fused (graph core0039) (root 2) 1 1) DegreeOneSmallSpectrum010.graph fusedMap0039=true := by decide +kernel
theorem certified0039 : Certified (graph core0039) (root 2) 1 1 :=
  of_native_maps core0039 DegreeOneSmallSpectrum015.graph DegreeOneSmallSpectrum010.graph
    sourceMap0039 fusedMap0039 sourceMap0039_checked fusedMap0039_checked
    DegreeOneSmallComparisons.comparison0039
#print axioms sourceMap0039_checked
#print axioms fusedMap0039_checked
#print axioms certified0039
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
