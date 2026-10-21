/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0516 : Family 7 := level7.get ⟨13,by decide⟩
def sourceMap0516 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0516 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0516_checked : acceptsGraphIso
    (source (graph core0516) (root 7) 0 3) DegreeOneSmallSpectrum921.graph sourceMap0516=true := by decide +kernel
theorem fusedMap0516_checked : acceptsGraphIso
    (fused (graph core0516) (root 7) 0 3) DegreeOneSmallSpectrum922.graph fusedMap0516=true := by decide +kernel
theorem certified0516 : Certified (graph core0516) (root 7) 0 3 :=
  of_native_maps core0516 DegreeOneSmallSpectrum921.graph DegreeOneSmallSpectrum922.graph
    sourceMap0516 fusedMap0516 sourceMap0516_checked fusedMap0516_checked
    DegreeOneSmallComparisons.comparison0516
#print axioms sourceMap0516_checked
#print axioms fusedMap0516_checked
#print axioms certified0516
def sourceMap0516swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0516swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0516swap_checked : acceptsGraphIso
    (source (graph core0516) (root 7) 3 0) DegreeOneSmallSpectrum921.graph sourceMap0516swap=true := by decide +kernel
theorem fusedMap0516swap_checked : acceptsGraphIso
    (fused (graph core0516) (root 7) 3 0) DegreeOneSmallSpectrum922.graph fusedMap0516swap=true := by decide +kernel
theorem certified0516swap : Certified (graph core0516) (root 7) 3 0 :=
  of_native_maps core0516 DegreeOneSmallSpectrum921.graph DegreeOneSmallSpectrum922.graph
    sourceMap0516swap fusedMap0516swap sourceMap0516swap_checked fusedMap0516swap_checked
    DegreeOneSmallComparisons.comparison0516
#print axioms sourceMap0516swap_checked
#print axioms fusedMap0516swap_checked
#print axioms certified0516swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
