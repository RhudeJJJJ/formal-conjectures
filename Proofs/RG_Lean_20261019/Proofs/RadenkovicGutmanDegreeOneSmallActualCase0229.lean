/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0229 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0229 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 2 2 v)
def fusedMap0229 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0229_checked : acceptsGraphIso
    (source (graph core0229) (root 5) 2 2) DegreeOneSmallSpectrum741.graph sourceMap0229=true := by decide +kernel
theorem fusedMap0229_checked : acceptsGraphIso
    (fused (graph core0229) (root 5) 2 2) DegreeOneSmallSpectrum371.graph fusedMap0229=true := by decide +kernel
theorem certified0229 : Certified (graph core0229) (root 5) 2 2 :=
  of_native_maps core0229 DegreeOneSmallSpectrum741.graph DegreeOneSmallSpectrum371.graph
    sourceMap0229 fusedMap0229 sourceMap0229_checked fusedMap0229_checked
    DegreeOneSmallComparisons.comparison0229
#print axioms sourceMap0229_checked
#print axioms fusedMap0229_checked
#print axioms certified0229
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
