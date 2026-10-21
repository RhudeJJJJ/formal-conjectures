/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0137 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0137 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap0137 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap0137_checked : acceptsGraphIso
    (source (graph core0137) (root 4) 1 4) DegreeOneSmallSpectrum540.graph sourceMap0137=true := by decide +kernel
theorem fusedMap0137_checked : acceptsGraphIso
    (fused (graph core0137) (root 4) 1 4) DegreeOneSmallSpectrum386.graph fusedMap0137=true := by decide +kernel
theorem certified0137 : Certified (graph core0137) (root 4) 1 4 :=
  of_native_maps core0137 DegreeOneSmallSpectrum540.graph DegreeOneSmallSpectrum386.graph
    sourceMap0137 fusedMap0137 sourceMap0137_checked fusedMap0137_checked
    DegreeOneSmallComparisons.comparison0137
#print axioms sourceMap0137_checked
#print axioms fusedMap0137_checked
#print axioms certified0137
def sourceMap0137swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,6,7] (sourceLabel 4 4 1 v)
def fusedMap0137swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap0137swap_checked : acceptsGraphIso
    (source (graph core0137) (root 4) 4 1) DegreeOneSmallSpectrum540.graph sourceMap0137swap=true := by decide +kernel
theorem fusedMap0137swap_checked : acceptsGraphIso
    (fused (graph core0137) (root 4) 4 1) DegreeOneSmallSpectrum386.graph fusedMap0137swap=true := by decide +kernel
theorem certified0137swap : Certified (graph core0137) (root 4) 4 1 :=
  of_native_maps core0137 DegreeOneSmallSpectrum540.graph DegreeOneSmallSpectrum386.graph
    sourceMap0137swap fusedMap0137swap sourceMap0137swap_checked fusedMap0137swap_checked
    DegreeOneSmallComparisons.comparison0137
#print axioms sourceMap0137swap_checked
#print axioms fusedMap0137swap_checked
#print axioms certified0137swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
