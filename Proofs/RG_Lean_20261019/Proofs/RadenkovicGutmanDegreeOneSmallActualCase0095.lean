/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0095 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0095 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![1,0,4,5,6,2,3] (sourceLabel 4 0 0 v)
def fusedMap0095 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![1,0,4,5,6,2,3] (fusedLabel 4 0 0 v)
theorem sourceMap0095_checked : acceptsGraphIso
    (source (graph core0095) (root 4) 0 0) DegreeOneSmallSpectrum008.graph sourceMap0095=true := by decide +kernel
theorem fusedMap0095_checked : acceptsGraphIso
    (fused (graph core0095) (root 4) 0 0) DegreeOneSmallSpectrum010.graph fusedMap0095=true := by decide +kernel
theorem certified0095 : Certified (graph core0095) (root 4) 0 0 :=
  of_native_maps core0095 DegreeOneSmallSpectrum008.graph DegreeOneSmallSpectrum010.graph
    sourceMap0095 fusedMap0095 sourceMap0095_checked fusedMap0095_checked
    DegreeOneSmallComparisons.comparison0095
#print axioms sourceMap0095_checked
#print axioms fusedMap0095_checked
#print axioms certified0095
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
