/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0124 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0124 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 4 2 3 v)
def fusedMap0124 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 2 3 v)
theorem sourceMap0124_checked : acceptsGraphIso
    (source (graph core0124) (root 4) 2 3) DegreeOneSmallSpectrum458.graph sourceMap0124=true := by decide +kernel
theorem fusedMap0124_checked : acceptsGraphIso
    (fused (graph core0124) (root 4) 2 3) DegreeOneSmallSpectrum378.graph fusedMap0124=true := by decide +kernel
theorem certified0124 : Certified (graph core0124) (root 4) 2 3 :=
  of_native_maps core0124 DegreeOneSmallSpectrum458.graph DegreeOneSmallSpectrum378.graph
    sourceMap0124 fusedMap0124 sourceMap0124_checked fusedMap0124_checked
    DegreeOneSmallComparisons.comparison0124
#print axioms sourceMap0124_checked
#print axioms fusedMap0124_checked
#print axioms certified0124
def sourceMap0124swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (sourceLabel 4 3 2 v)
def fusedMap0124swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 3 2 v)
theorem sourceMap0124swap_checked : acceptsGraphIso
    (source (graph core0124) (root 4) 3 2) DegreeOneSmallSpectrum458.graph sourceMap0124swap=true := by decide +kernel
theorem fusedMap0124swap_checked : acceptsGraphIso
    (fused (graph core0124) (root 4) 3 2) DegreeOneSmallSpectrum378.graph fusedMap0124swap=true := by decide +kernel
theorem certified0124swap : Certified (graph core0124) (root 4) 3 2 :=
  of_native_maps core0124 DegreeOneSmallSpectrum458.graph DegreeOneSmallSpectrum378.graph
    sourceMap0124swap fusedMap0124swap sourceMap0124swap_checked fusedMap0124swap_checked
    DegreeOneSmallComparisons.comparison0124
#print axioms sourceMap0124swap_checked
#print axioms fusedMap0124swap_checked
#print axioms certified0124swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
