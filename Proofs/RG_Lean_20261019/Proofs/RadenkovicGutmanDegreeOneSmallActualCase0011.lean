/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0011 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0011 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,3,1,2,4,5,6] (sourceLabel 1 1 2 v)
def fusedMap0011 : (Vertices 1 ⊕ Fin 5) → Fin 7 :=
  fun v => ![2,3,1,0,4,5,6] (fusedLabel 1 1 2 v)
theorem sourceMap0011_checked : acceptsGraphIso
    (source (graph core0011) (root 1) 1 2) DegreeOneSmallSpectrum009.graph sourceMap0011=true := by decide +kernel
theorem fusedMap0011_checked : acceptsGraphIso
    (fused (graph core0011) (root 1) 1 2) DegreeOneSmallSpectrum010.graph fusedMap0011=true := by decide +kernel
theorem certified0011 : Certified (graph core0011) (root 1) 1 2 :=
  of_native_maps core0011 DegreeOneSmallSpectrum009.graph DegreeOneSmallSpectrum010.graph
    sourceMap0011 fusedMap0011 sourceMap0011_checked fusedMap0011_checked
    DegreeOneSmallComparisons.comparison0011
#print axioms sourceMap0011_checked
#print axioms fusedMap0011_checked
#print axioms certified0011
def sourceMap0011swap : (Vertices 1 ⊕ Fin 3 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,3,4,5,6,1,2] (sourceLabel 1 2 1 v)
def fusedMap0011swap : (Vertices 1 ⊕ Fin 5) → Fin 7 :=
  fun v => ![2,3,1,0,4,5,6] (fusedLabel 1 2 1 v)
theorem sourceMap0011swap_checked : acceptsGraphIso
    (source (graph core0011) (root 1) 2 1) DegreeOneSmallSpectrum009.graph sourceMap0011swap=true := by decide +kernel
theorem fusedMap0011swap_checked : acceptsGraphIso
    (fused (graph core0011) (root 1) 2 1) DegreeOneSmallSpectrum010.graph fusedMap0011swap=true := by decide +kernel
theorem certified0011swap : Certified (graph core0011) (root 1) 2 1 :=
  of_native_maps core0011 DegreeOneSmallSpectrum009.graph DegreeOneSmallSpectrum010.graph
    sourceMap0011swap fusedMap0011swap sourceMap0011swap_checked fusedMap0011swap_checked
    DegreeOneSmallComparisons.comparison0011
#print axioms sourceMap0011swap_checked
#print axioms fusedMap0011swap_checked
#print axioms certified0011swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
