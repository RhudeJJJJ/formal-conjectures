/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0071 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0071 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 3 2 4 v)
def fusedMap0071 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 2 4 v)
theorem sourceMap0071_checked : acceptsGraphIso
    (source (graph core0071) (root 3) 2 4) DegreeOneSmallSpectrum563.graph sourceMap0071=true := by decide +kernel
theorem fusedMap0071_checked : acceptsGraphIso
    (fused (graph core0071) (root 3) 2 4) DegreeOneSmallSpectrum369.graph fusedMap0071=true := by decide +kernel
theorem certified0071 : Certified (graph core0071) (root 3) 2 4 :=
  of_native_maps core0071 DegreeOneSmallSpectrum563.graph DegreeOneSmallSpectrum369.graph
    sourceMap0071 fusedMap0071 sourceMap0071_checked fusedMap0071_checked
    DegreeOneSmallComparisons.comparison0071
#print axioms sourceMap0071_checked
#print axioms fusedMap0071_checked
#print axioms certified0071
def sourceMap0071swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,2,3,4,0,8,9,10,11,5,6,7] (sourceLabel 3 4 2 v)
def fusedMap0071swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 4 2 v)
theorem sourceMap0071swap_checked : acceptsGraphIso
    (source (graph core0071) (root 3) 4 2) DegreeOneSmallSpectrum563.graph sourceMap0071swap=true := by decide +kernel
theorem fusedMap0071swap_checked : acceptsGraphIso
    (fused (graph core0071) (root 3) 4 2) DegreeOneSmallSpectrum369.graph fusedMap0071swap=true := by decide +kernel
theorem certified0071swap : Certified (graph core0071) (root 3) 4 2 :=
  of_native_maps core0071 DegreeOneSmallSpectrum563.graph DegreeOneSmallSpectrum369.graph
    sourceMap0071swap fusedMap0071swap sourceMap0071swap_checked fusedMap0071swap_checked
    DegreeOneSmallComparisons.comparison0071
#print axioms sourceMap0071swap_checked
#print axioms fusedMap0071swap_checked
#print axioms certified0071swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
