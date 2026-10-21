/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0002 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0002 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 3) → Fin 6 :=
  fun v => ![1,2,3,0,4,5] (sourceLabel 1 0 2 v)
def fusedMap0002 : (Vertices 1 ⊕ Fin 4) → Fin 6 :=
  fun v => ![1,2,0,3,4,5] (fusedLabel 1 0 2 v)
theorem sourceMap0002_checked : acceptsGraphIso
    (source (graph core0002) (root 1) 0 2) DegreeOneSmallSpectrum006.graph sourceMap0002=true := by decide +kernel
theorem fusedMap0002_checked : acceptsGraphIso
    (fused (graph core0002) (root 1) 0 2) DegreeOneSmallSpectrum004.graph fusedMap0002=true := by decide +kernel
theorem certified0002 : Certified (graph core0002) (root 1) 0 2 :=
  of_native_maps core0002 DegreeOneSmallSpectrum006.graph DegreeOneSmallSpectrum004.graph
    sourceMap0002 fusedMap0002 sourceMap0002_checked fusedMap0002_checked
    DegreeOneSmallComparisons.comparison0002
#print axioms sourceMap0002_checked
#print axioms fusedMap0002_checked
#print axioms certified0002
def sourceMap0002swap : (Vertices 1 ⊕ Fin 3 ⊕ Fin 1) → Fin 6 :=
  fun v => ![1,2,0,4,5,3] (sourceLabel 1 2 0 v)
def fusedMap0002swap : (Vertices 1 ⊕ Fin 4) → Fin 6 :=
  fun v => ![1,2,0,3,4,5] (fusedLabel 1 2 0 v)
theorem sourceMap0002swap_checked : acceptsGraphIso
    (source (graph core0002) (root 1) 2 0) DegreeOneSmallSpectrum006.graph sourceMap0002swap=true := by decide +kernel
theorem fusedMap0002swap_checked : acceptsGraphIso
    (fused (graph core0002) (root 1) 2 0) DegreeOneSmallSpectrum004.graph fusedMap0002swap=true := by decide +kernel
theorem certified0002swap : Certified (graph core0002) (root 1) 2 0 :=
  of_native_maps core0002 DegreeOneSmallSpectrum006.graph DegreeOneSmallSpectrum004.graph
    sourceMap0002swap fusedMap0002swap sourceMap0002swap_checked fusedMap0002swap_checked
    DegreeOneSmallComparisons.comparison0002
#print axioms sourceMap0002swap_checked
#print axioms fusedMap0002swap_checked
#print axioms certified0002swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
