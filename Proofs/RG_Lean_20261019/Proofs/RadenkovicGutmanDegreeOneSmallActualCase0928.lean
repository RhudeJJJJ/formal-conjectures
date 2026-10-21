/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0928 : Family 8 := level8.get ⟨65,by decide⟩
def sourceMap0928 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0928 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap0928_checked : acceptsGraphIso
    (source (graph core0928) (root 8) 0 1) DegreeOneSmallSpectrum538.graph sourceMap0928=true := by decide +kernel
theorem fusedMap0928_checked : acceptsGraphIso
    (fused (graph core0928) (root 8) 0 1) DegreeOneSmallSpectrum559.graph fusedMap0928=true := by decide +kernel
theorem certified0928 : Certified (graph core0928) (root 8) 0 1 :=
  of_native_maps core0928 DegreeOneSmallSpectrum538.graph DegreeOneSmallSpectrum559.graph
    sourceMap0928 fusedMap0928 sourceMap0928_checked fusedMap0928_checked
    DegreeOneSmallComparisons.comparison0928
#print axioms sourceMap0928_checked
#print axioms fusedMap0928_checked
#print axioms certified0928
def sourceMap0928swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0928swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap0928swap_checked : acceptsGraphIso
    (source (graph core0928) (root 8) 1 0) DegreeOneSmallSpectrum538.graph sourceMap0928swap=true := by decide +kernel
theorem fusedMap0928swap_checked : acceptsGraphIso
    (fused (graph core0928) (root 8) 1 0) DegreeOneSmallSpectrum559.graph fusedMap0928swap=true := by decide +kernel
theorem certified0928swap : Certified (graph core0928) (root 8) 1 0 :=
  of_native_maps core0928 DegreeOneSmallSpectrum538.graph DegreeOneSmallSpectrum559.graph
    sourceMap0928swap fusedMap0928swap sourceMap0928swap_checked fusedMap0928swap_checked
    DegreeOneSmallComparisons.comparison0928
#print axioms sourceMap0928swap_checked
#print axioms fusedMap0928swap_checked
#print axioms certified0928swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
