/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0830 : Family 8 := level8.get ⟨27,by decide⟩
def sourceMap0830 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0830 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 1 1 v)
theorem sourceMap0830_checked : acceptsGraphIso
    (source (graph core0830) (root 8) 1 1) DegreeOneSmallSpectrum1331.graph sourceMap0830=true := by decide +kernel
theorem fusedMap0830_checked : acceptsGraphIso
    (fused (graph core0830) (root 8) 1 1) DegreeOneSmallSpectrum976.graph fusedMap0830=true := by decide +kernel
theorem certified0830 : Certified (graph core0830) (root 8) 1 1 :=
  of_native_maps core0830 DegreeOneSmallSpectrum1331.graph DegreeOneSmallSpectrum976.graph
    sourceMap0830 fusedMap0830 sourceMap0830_checked fusedMap0830_checked
    DegreeOneSmallComparisons.comparison0830
#print axioms sourceMap0830_checked
#print axioms fusedMap0830_checked
#print axioms certified0830
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
