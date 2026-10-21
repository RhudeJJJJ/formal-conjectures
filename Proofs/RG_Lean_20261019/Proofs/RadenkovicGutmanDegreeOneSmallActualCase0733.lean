/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0733 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0733 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0733 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0733_checked : acceptsGraphIso
    (source (graph core0733) (root 7) 1 1) SmallGeFourSpectrum206.graph sourceMap0733=true := by decide +kernel
theorem fusedMap0733_checked : acceptsGraphIso
    (fused (graph core0733) (root 7) 1 1) SmallGeFourSpectrum116.graph fusedMap0733=true := by decide +kernel
theorem certified0733 : Certified (graph core0733) (root 7) 1 1 :=
  of_native_maps core0733 SmallGeFourSpectrum206.graph SmallGeFourSpectrum116.graph
    sourceMap0733 fusedMap0733 sourceMap0733_checked fusedMap0733_checked
    DegreeOneSmallComparisons.comparison0733
#print axioms sourceMap0733_checked
#print axioms fusedMap0733_checked
#print axioms certified0733
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
