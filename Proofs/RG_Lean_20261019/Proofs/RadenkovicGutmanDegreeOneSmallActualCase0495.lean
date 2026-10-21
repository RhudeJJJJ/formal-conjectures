/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0495 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0495 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0495 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0495_checked : acceptsGraphIso
    (source (graph core0495) (root 7) 0 0) DegreeOneSmallSpectrum122.graph sourceMap0495=true := by decide +kernel
theorem fusedMap0495_checked : acceptsGraphIso
    (fused (graph core0495) (root 7) 0 0) DegreeOneSmallSpectrum076.graph fusedMap0495=true := by decide +kernel
theorem certified0495 : Certified (graph core0495) (root 7) 0 0 :=
  of_native_maps core0495 DegreeOneSmallSpectrum122.graph DegreeOneSmallSpectrum076.graph
    sourceMap0495 fusedMap0495 sourceMap0495_checked fusedMap0495_checked
    DegreeOneSmallComparisons.comparison0495
#print axioms sourceMap0495_checked
#print axioms fusedMap0495_checked
#print axioms certified0495
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
