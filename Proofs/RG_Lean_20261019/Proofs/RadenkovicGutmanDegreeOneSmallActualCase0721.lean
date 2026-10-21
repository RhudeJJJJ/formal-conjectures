/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0721 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0721 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0721 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0721_checked : acceptsGraphIso
    (source (graph core0721) (root 7) 1 1) SmallGeFourSpectrum170.graph sourceMap0721=true := by decide +kernel
theorem fusedMap0721_checked : acceptsGraphIso
    (fused (graph core0721) (root 7) 1 1) SmallGeFourSpectrum099.graph fusedMap0721=true := by decide +kernel
theorem certified0721 : Certified (graph core0721) (root 7) 1 1 :=
  of_native_maps core0721 SmallGeFourSpectrum170.graph SmallGeFourSpectrum099.graph
    sourceMap0721 fusedMap0721 sourceMap0721_checked fusedMap0721_checked
    DegreeOneSmallComparisons.comparison0721
#print axioms sourceMap0721_checked
#print axioms fusedMap0721_checked
#print axioms certified0721
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
