/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0081 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0081 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (sourceLabel 3 0 6 v)
def fusedMap0081 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 0 6 v)
theorem sourceMap0081_checked : acceptsGraphIso
    (source (graph core0081) (root 3) 0 6) DegreeOneSmallSpectrum371.graph sourceMap0081=true := by decide +kernel
theorem fusedMap0081_checked : acceptsGraphIso
    (fused (graph core0081) (root 3) 0 6) DegreeOneSmallSpectrum378.graph fusedMap0081=true := by decide +kernel
theorem certified0081 : Certified (graph core0081) (root 3) 0 6 :=
  of_native_maps core0081 DegreeOneSmallSpectrum371.graph DegreeOneSmallSpectrum378.graph
    sourceMap0081 fusedMap0081 sourceMap0081_checked fusedMap0081_checked
    DegreeOneSmallComparisons.comparison0081
#print axioms sourceMap0081_checked
#print axioms fusedMap0081_checked
#print axioms certified0081
def sourceMap0081swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,11,6] (sourceLabel 3 6 0 v)
def fusedMap0081swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 6 0 v)
theorem sourceMap0081swap_checked : acceptsGraphIso
    (source (graph core0081) (root 3) 6 0) DegreeOneSmallSpectrum371.graph sourceMap0081swap=true := by decide +kernel
theorem fusedMap0081swap_checked : acceptsGraphIso
    (fused (graph core0081) (root 3) 6 0) DegreeOneSmallSpectrum378.graph fusedMap0081swap=true := by decide +kernel
theorem certified0081swap : Certified (graph core0081) (root 3) 6 0 :=
  of_native_maps core0081 DegreeOneSmallSpectrum371.graph DegreeOneSmallSpectrum378.graph
    sourceMap0081swap fusedMap0081swap sourceMap0081swap_checked fusedMap0081swap_checked
    DegreeOneSmallComparisons.comparison0081
#print axioms sourceMap0081swap_checked
#print axioms fusedMap0081swap_checked
#print axioms certified0081swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
