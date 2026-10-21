/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0687 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0687 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (sourceLabel 7 0 0 v)
def fusedMap0687 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0687_checked : acceptsGraphIso
    (source (graph core0687) (root 7) 0 0) DegreeOneSmallSpectrum157.graph sourceMap0687=true := by decide +kernel
theorem fusedMap0687_checked : acceptsGraphIso
    (fused (graph core0687) (root 7) 0 0) DegreeOneSmallSpectrum098.graph fusedMap0687=true := by decide +kernel
theorem certified0687 : Certified (graph core0687) (root 7) 0 0 :=
  of_native_maps core0687 DegreeOneSmallSpectrum157.graph DegreeOneSmallSpectrum098.graph
    sourceMap0687 fusedMap0687 sourceMap0687_checked fusedMap0687_checked
    DegreeOneSmallComparisons.comparison0687
#print axioms sourceMap0687_checked
#print axioms fusedMap0687_checked
#print axioms certified0687
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
