/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0125 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0125 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap0125 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap0125_checked : acceptsGraphIso
    (source (graph core0125) (root 4) 2 4) DegreeOneSmallSpectrum1189.graph sourceMap0125=true := by decide +kernel
theorem fusedMap0125_checked : acceptsGraphIso
    (fused (graph core0125) (root 4) 2 4) DegreeOneSmallSpectrum856.graph fusedMap0125=true := by decide +kernel
theorem certified0125 : Certified (graph core0125) (root 4) 2 4 :=
  of_native_maps core0125 DegreeOneSmallSpectrum1189.graph DegreeOneSmallSpectrum856.graph
    sourceMap0125 fusedMap0125 sourceMap0125_checked fusedMap0125_checked
    DegreeOneSmallComparisons.comparison0125
#print axioms sourceMap0125_checked
#print axioms fusedMap0125_checked
#print axioms certified0125
def sourceMap0125swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,2,3,4,5,0,9,10,11,12,6,7,8] (sourceLabel 4 4 2 v)
def fusedMap0125swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap0125swap_checked : acceptsGraphIso
    (source (graph core0125) (root 4) 4 2) DegreeOneSmallSpectrum1189.graph sourceMap0125swap=true := by decide +kernel
theorem fusedMap0125swap_checked : acceptsGraphIso
    (fused (graph core0125) (root 4) 4 2) DegreeOneSmallSpectrum856.graph fusedMap0125swap=true := by decide +kernel
theorem certified0125swap : Certified (graph core0125) (root 4) 4 2 :=
  of_native_maps core0125 DegreeOneSmallSpectrum1189.graph DegreeOneSmallSpectrum856.graph
    sourceMap0125swap fusedMap0125swap sourceMap0125swap_checked fusedMap0125swap_checked
    DegreeOneSmallComparisons.comparison0125
#print axioms sourceMap0125swap_checked
#print axioms fusedMap0125swap_checked
#print axioms certified0125swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
