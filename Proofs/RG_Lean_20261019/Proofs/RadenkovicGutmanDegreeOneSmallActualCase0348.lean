/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0348 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0348 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (sourceLabel 6 0 0 v)
def fusedMap0348 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0348_checked : acceptsGraphIso
    (source (graph core0348) (root 6) 0 0) DegreeOneSmallSpectrum050.graph sourceMap0348=true := by decide +kernel
theorem fusedMap0348_checked : acceptsGraphIso
    (fused (graph core0348) (root 6) 0 0) DegreeOneSmallSpectrum058.graph fusedMap0348=true := by decide +kernel
theorem certified0348 : Certified (graph core0348) (root 6) 0 0 :=
  of_native_maps core0348 DegreeOneSmallSpectrum050.graph DegreeOneSmallSpectrum058.graph
    sourceMap0348 fusedMap0348 sourceMap0348_checked fusedMap0348_checked
    DegreeOneSmallComparisons.comparison0348
#print axioms sourceMap0348_checked
#print axioms fusedMap0348_checked
#print axioms certified0348
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
