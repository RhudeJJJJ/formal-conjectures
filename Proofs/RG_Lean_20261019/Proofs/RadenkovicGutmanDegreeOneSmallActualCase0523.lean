/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0523 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0523 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0523 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0523_checked : acceptsGraphIso
    (source (graph core0523) (root 7) 1 1) DegreeOneSmallSpectrum513.graph sourceMap0523=true := by decide +kernel
theorem fusedMap0523_checked : acceptsGraphIso
    (fused (graph core0523) (root 7) 1 1) DegreeOneSmallSpectrum381.graph fusedMap0523=true := by decide +kernel
theorem certified0523 : Certified (graph core0523) (root 7) 1 1 :=
  of_native_maps core0523 DegreeOneSmallSpectrum513.graph DegreeOneSmallSpectrum381.graph
    sourceMap0523 fusedMap0523 sourceMap0523_checked fusedMap0523_checked
    DegreeOneSmallComparisons.comparison0523
#print axioms sourceMap0523_checked
#print axioms fusedMap0523_checked
#print axioms certified0523
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
