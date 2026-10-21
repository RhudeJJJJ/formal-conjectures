/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0717 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0717 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0717 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0717_checked : acceptsGraphIso
    (source (graph core0717) (root 7) 0 0) SmallGeFourSpectrum031.graph sourceMap0717=true := by decide +kernel
theorem fusedMap0717_checked : acceptsGraphIso
    (fused (graph core0717) (root 7) 0 0) SmallGeFourSpectrum019.graph fusedMap0717=true := by decide +kernel
theorem certified0717 : Certified (graph core0717) (root 7) 0 0 :=
  of_native_maps core0717 SmallGeFourSpectrum031.graph SmallGeFourSpectrum019.graph
    sourceMap0717 fusedMap0717 sourceMap0717_checked fusedMap0717_checked
    DegreeOneSmallComparisons.comparison0717
#print axioms sourceMap0717_checked
#print axioms fusedMap0717_checked
#print axioms certified0717
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
