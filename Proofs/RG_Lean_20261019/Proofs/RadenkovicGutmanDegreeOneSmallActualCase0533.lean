/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0533 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0533 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0533 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0533_checked : acceptsGraphIso
    (source (graph core0533) (root 7) 0 2) DegreeOneSmallSpectrum574.graph sourceMap0533=true := by decide +kernel
theorem fusedMap0533_checked : acceptsGraphIso
    (fused (graph core0533) (root 7) 0 2) DegreeOneSmallSpectrum387.graph fusedMap0533=true := by decide +kernel
theorem certified0533 : Certified (graph core0533) (root 7) 0 2 :=
  of_native_maps core0533 DegreeOneSmallSpectrum574.graph DegreeOneSmallSpectrum387.graph
    sourceMap0533 fusedMap0533 sourceMap0533_checked fusedMap0533_checked
    DegreeOneSmallComparisons.comparison0533
#print axioms sourceMap0533_checked
#print axioms fusedMap0533_checked
#print axioms certified0533
def sourceMap0533swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0533swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0533swap_checked : acceptsGraphIso
    (source (graph core0533) (root 7) 2 0) DegreeOneSmallSpectrum574.graph sourceMap0533swap=true := by decide +kernel
theorem fusedMap0533swap_checked : acceptsGraphIso
    (fused (graph core0533) (root 7) 2 0) DegreeOneSmallSpectrum387.graph fusedMap0533swap=true := by decide +kernel
theorem certified0533swap : Certified (graph core0533) (root 7) 2 0 :=
  of_native_maps core0533 DegreeOneSmallSpectrum574.graph DegreeOneSmallSpectrum387.graph
    sourceMap0533swap fusedMap0533swap sourceMap0533swap_checked fusedMap0533swap_checked
    DegreeOneSmallComparisons.comparison0533
#print axioms sourceMap0533swap_checked
#print axioms fusedMap0533swap_checked
#print axioms certified0533swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
