/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0727 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0727 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,5,6,7,8,9,10,11,1,2,3,4] (sourceLabel 7 1 1 v)
def fusedMap0727 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0727_checked : acceptsGraphIso
    (source (graph core0727) (root 7) 1 1) SmallGeFourSpectrum175.graph sourceMap0727=true := by decide +kernel
theorem fusedMap0727_checked : acceptsGraphIso
    (fused (graph core0727) (root 7) 1 1) SmallGeFourSpectrum100.graph fusedMap0727=true := by decide +kernel
theorem certified0727 : Certified (graph core0727) (root 7) 1 1 :=
  of_native_maps core0727 SmallGeFourSpectrum175.graph SmallGeFourSpectrum100.graph
    sourceMap0727 fusedMap0727 sourceMap0727_checked fusedMap0727_checked
    DegreeOneSmallComparisons.comparison0727
#print axioms sourceMap0727_checked
#print axioms fusedMap0727_checked
#print axioms certified0727
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
