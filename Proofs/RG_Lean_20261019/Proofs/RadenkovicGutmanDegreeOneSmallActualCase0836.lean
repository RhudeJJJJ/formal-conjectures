/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0836 : Family 8 := level8.get ⟨30,by decide⟩
def sourceMap0836 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0836 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0836_checked : acceptsGraphIso
    (source (graph core0836) (root 8) 0 1) DegreeOneSmallSpectrum544.graph sourceMap0836=true := by decide +kernel
theorem fusedMap0836_checked : acceptsGraphIso
    (fused (graph core0836) (root 8) 0 1) DegreeOneSmallSpectrum394.graph fusedMap0836=true := by decide +kernel
theorem certified0836 : Certified (graph core0836) (root 8) 0 1 :=
  of_native_maps core0836 DegreeOneSmallSpectrum544.graph DegreeOneSmallSpectrum394.graph
    sourceMap0836 fusedMap0836 sourceMap0836_checked fusedMap0836_checked
    DegreeOneSmallComparisons.comparison0836
#print axioms sourceMap0836_checked
#print axioms fusedMap0836_checked
#print axioms certified0836
def sourceMap0836swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0836swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0836swap_checked : acceptsGraphIso
    (source (graph core0836) (root 8) 1 0) DegreeOneSmallSpectrum544.graph sourceMap0836swap=true := by decide +kernel
theorem fusedMap0836swap_checked : acceptsGraphIso
    (fused (graph core0836) (root 8) 1 0) DegreeOneSmallSpectrum394.graph fusedMap0836swap=true := by decide +kernel
theorem certified0836swap : Certified (graph core0836) (root 8) 1 0 :=
  of_native_maps core0836 DegreeOneSmallSpectrum544.graph DegreeOneSmallSpectrum394.graph
    sourceMap0836swap fusedMap0836swap sourceMap0836swap_checked fusedMap0836swap_checked
    DegreeOneSmallComparisons.comparison0836
#print axioms sourceMap0836swap_checked
#print axioms fusedMap0836swap_checked
#print axioms certified0836swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
