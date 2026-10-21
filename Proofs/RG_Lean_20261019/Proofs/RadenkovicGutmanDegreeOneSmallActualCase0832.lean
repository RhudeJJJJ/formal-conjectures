/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0832 : Family 8 := level8.get ⟨29,by decide⟩
def sourceMap0832 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0832 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0832_checked : acceptsGraphIso
    (source (graph core0832) (root 8) 0 1) DegreeOneSmallSpectrum540.graph sourceMap0832=true := by decide +kernel
theorem fusedMap0832_checked : acceptsGraphIso
    (fused (graph core0832) (root 8) 0 1) DegreeOneSmallSpectrum393.graph fusedMap0832=true := by decide +kernel
theorem certified0832 : Certified (graph core0832) (root 8) 0 1 :=
  of_native_maps core0832 DegreeOneSmallSpectrum540.graph DegreeOneSmallSpectrum393.graph
    sourceMap0832 fusedMap0832 sourceMap0832_checked fusedMap0832_checked
    DegreeOneSmallComparisons.comparison0832
#print axioms sourceMap0832_checked
#print axioms fusedMap0832_checked
#print axioms certified0832
def sourceMap0832swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0832swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0832swap_checked : acceptsGraphIso
    (source (graph core0832) (root 8) 1 0) DegreeOneSmallSpectrum540.graph sourceMap0832swap=true := by decide +kernel
theorem fusedMap0832swap_checked : acceptsGraphIso
    (fused (graph core0832) (root 8) 1 0) DegreeOneSmallSpectrum393.graph fusedMap0832swap=true := by decide +kernel
theorem certified0832swap : Certified (graph core0832) (root 8) 1 0 :=
  of_native_maps core0832 DegreeOneSmallSpectrum540.graph DegreeOneSmallSpectrum393.graph
    sourceMap0832swap fusedMap0832swap sourceMap0832swap_checked fusedMap0832swap_checked
    DegreeOneSmallComparisons.comparison0832
#print axioms sourceMap0832swap_checked
#print axioms fusedMap0832swap_checked
#print axioms certified0832swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
