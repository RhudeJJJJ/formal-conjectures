/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0901 : Family 8 := level8.get ⟨55,by decide⟩
def sourceMap0901 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0901 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0901_checked : acceptsGraphIso
    (source (graph core0901) (root 8) 0 2) DegreeOneSmallSpectrum1346.graph sourceMap0901=true := by decide +kernel
theorem fusedMap0901_checked : acceptsGraphIso
    (fused (graph core0901) (root 8) 0 2) DegreeOneSmallSpectrum911.graph fusedMap0901=true := by decide +kernel
theorem certified0901 : Certified (graph core0901) (root 8) 0 2 :=
  of_native_maps core0901 DegreeOneSmallSpectrum1346.graph DegreeOneSmallSpectrum911.graph
    sourceMap0901 fusedMap0901 sourceMap0901_checked fusedMap0901_checked
    DegreeOneSmallComparisons.comparison0901
#print axioms sourceMap0901_checked
#print axioms fusedMap0901_checked
#print axioms certified0901
def sourceMap0901swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0901swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0901swap_checked : acceptsGraphIso
    (source (graph core0901) (root 8) 2 0) DegreeOneSmallSpectrum1346.graph sourceMap0901swap=true := by decide +kernel
theorem fusedMap0901swap_checked : acceptsGraphIso
    (fused (graph core0901) (root 8) 2 0) DegreeOneSmallSpectrum911.graph fusedMap0901swap=true := by decide +kernel
theorem certified0901swap : Certified (graph core0901) (root 8) 2 0 :=
  of_native_maps core0901 DegreeOneSmallSpectrum1346.graph DegreeOneSmallSpectrum911.graph
    sourceMap0901swap fusedMap0901swap sourceMap0901swap_checked fusedMap0901swap_checked
    DegreeOneSmallComparisons.comparison0901
#print axioms sourceMap0901swap_checked
#print axioms fusedMap0901swap_checked
#print axioms certified0901swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
