/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0919 : Family 8 := level8.get ⟨62,by decide⟩
def sourceMap0919 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0919 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0919_checked : acceptsGraphIso
    (source (graph core0919) (root 8) 0 0) DegreeOneSmallSpectrum311.graph sourceMap0919=true := by decide +kernel
theorem fusedMap0919_checked : acceptsGraphIso
    (fused (graph core0919) (root 8) 0 0) DegreeOneSmallSpectrum209.graph fusedMap0919=true := by decide +kernel
theorem certified0919 : Certified (graph core0919) (root 8) 0 0 :=
  of_native_maps core0919 DegreeOneSmallSpectrum311.graph DegreeOneSmallSpectrum209.graph
    sourceMap0919 fusedMap0919 sourceMap0919_checked fusedMap0919_checked
    DegreeOneSmallComparisons.comparison0919
#print axioms sourceMap0919_checked
#print axioms fusedMap0919_checked
#print axioms certified0919
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
