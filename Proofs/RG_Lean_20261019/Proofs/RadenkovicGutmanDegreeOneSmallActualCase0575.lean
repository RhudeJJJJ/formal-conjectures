/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0575 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0575 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0575 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0575_checked : acceptsGraphIso
    (source (graph core0575) (root 7) 0 2) DegreeOneSmallSpectrum416.graph sourceMap0575=true := by decide +kernel
theorem fusedMap0575_checked : acceptsGraphIso
    (fused (graph core0575) (root 7) 0 2) DegreeOneSmallSpectrum417.graph fusedMap0575=true := by decide +kernel
theorem certified0575 : Certified (graph core0575) (root 7) 0 2 :=
  of_native_maps core0575 DegreeOneSmallSpectrum416.graph DegreeOneSmallSpectrum417.graph
    sourceMap0575 fusedMap0575 sourceMap0575_checked fusedMap0575_checked
    DegreeOneSmallComparisons.comparison0575
#print axioms sourceMap0575_checked
#print axioms fusedMap0575_checked
#print axioms certified0575
def sourceMap0575swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0575swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0575swap_checked : acceptsGraphIso
    (source (graph core0575) (root 7) 2 0) DegreeOneSmallSpectrum416.graph sourceMap0575swap=true := by decide +kernel
theorem fusedMap0575swap_checked : acceptsGraphIso
    (fused (graph core0575) (root 7) 2 0) DegreeOneSmallSpectrum417.graph fusedMap0575swap=true := by decide +kernel
theorem certified0575swap : Certified (graph core0575) (root 7) 2 0 :=
  of_native_maps core0575 DegreeOneSmallSpectrum416.graph DegreeOneSmallSpectrum417.graph
    sourceMap0575swap fusedMap0575swap sourceMap0575swap_checked fusedMap0575swap_checked
    DegreeOneSmallComparisons.comparison0575
#print axioms sourceMap0575swap_checked
#print axioms fusedMap0575swap_checked
#print axioms certified0575swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
