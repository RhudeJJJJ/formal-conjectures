/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0455 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0455 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0455 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0455_checked : acceptsGraphIso
    (source (graph core0455) (root 7) 0 2) DegreeOneSmallSpectrum376.graph sourceMap0455=true := by decide +kernel
theorem fusedMap0455_checked : acceptsGraphIso
    (fused (graph core0455) (root 7) 0 2) DegreeOneSmallSpectrum378.graph fusedMap0455=true := by decide +kernel
theorem certified0455 : Certified (graph core0455) (root 7) 0 2 :=
  of_native_maps core0455 DegreeOneSmallSpectrum376.graph DegreeOneSmallSpectrum378.graph
    sourceMap0455 fusedMap0455 sourceMap0455_checked fusedMap0455_checked
    DegreeOneSmallComparisons.comparison0455
#print axioms sourceMap0455_checked
#print axioms fusedMap0455_checked
#print axioms certified0455
def sourceMap0455swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0455swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0455swap_checked : acceptsGraphIso
    (source (graph core0455) (root 7) 2 0) DegreeOneSmallSpectrum376.graph sourceMap0455swap=true := by decide +kernel
theorem fusedMap0455swap_checked : acceptsGraphIso
    (fused (graph core0455) (root 7) 2 0) DegreeOneSmallSpectrum378.graph fusedMap0455swap=true := by decide +kernel
theorem certified0455swap : Certified (graph core0455) (root 7) 2 0 :=
  of_native_maps core0455 DegreeOneSmallSpectrum376.graph DegreeOneSmallSpectrum378.graph
    sourceMap0455swap fusedMap0455swap sourceMap0455swap_checked fusedMap0455swap_checked
    DegreeOneSmallComparisons.comparison0455
#print axioms sourceMap0455swap_checked
#print axioms fusedMap0455swap_checked
#print axioms certified0455swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
