/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0749 : Family 8 := level8.get ⟨3,by decide⟩
def sourceMap0749 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 8 0 2 v)
def fusedMap0749 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0749_checked : acceptsGraphIso
    (source (graph core0749) (root 8) 0 2) DegreeOneSmallSpectrum962.graph sourceMap0749=true := by decide +kernel
theorem fusedMap0749_checked : acceptsGraphIso
    (fused (graph core0749) (root 8) 0 2) DegreeOneSmallSpectrum858.graph fusedMap0749=true := by decide +kernel
theorem certified0749 : Certified (graph core0749) (root 8) 0 2 :=
  of_native_maps core0749 DegreeOneSmallSpectrum962.graph DegreeOneSmallSpectrum858.graph
    sourceMap0749 fusedMap0749 sourceMap0749_checked fusedMap0749_checked
    DegreeOneSmallComparisons.comparison0749
#print axioms sourceMap0749_checked
#print axioms fusedMap0749_checked
#print axioms certified0749
def sourceMap0749swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 2 0 v)
def fusedMap0749swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0749swap_checked : acceptsGraphIso
    (source (graph core0749) (root 8) 2 0) DegreeOneSmallSpectrum962.graph sourceMap0749swap=true := by decide +kernel
theorem fusedMap0749swap_checked : acceptsGraphIso
    (fused (graph core0749) (root 8) 2 0) DegreeOneSmallSpectrum858.graph fusedMap0749swap=true := by decide +kernel
theorem certified0749swap : Certified (graph core0749) (root 8) 2 0 :=
  of_native_maps core0749 DegreeOneSmallSpectrum962.graph DegreeOneSmallSpectrum858.graph
    sourceMap0749swap fusedMap0749swap sourceMap0749swap_checked fusedMap0749swap_checked
    DegreeOneSmallComparisons.comparison0749
#print axioms sourceMap0749swap_checked
#print axioms fusedMap0749swap_checked
#print axioms certified0749swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
