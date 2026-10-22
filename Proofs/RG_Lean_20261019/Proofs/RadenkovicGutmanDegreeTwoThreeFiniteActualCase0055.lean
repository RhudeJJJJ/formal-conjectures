/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0055 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap0055 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0055 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap0055_checked : acceptsGraphIso
    (source (graph core0055) (root 7) 0 0) DegreeOneSmallSpectrum135.graph sourceMap0055=true := by decide +kernel
theorem fusedMap0055_checked : acceptsGraphIso
    (fused (graph core0055) (root 7) 0 0) DegreeOneSmallSpectrum134.graph fusedMap0055=true := by decide +kernel
theorem certified0055 : Certified (graph core0055) (root 7) 0 0 :=
  of_native_maps core0055 DegreeOneSmallSpectrum135.graph DegreeOneSmallSpectrum134.graph
    sourceMap0055 fusedMap0055 sourceMap0055_checked fusedMap0055_checked
    DegreeTwoThreeFiniteComparisons.comparison0055
#print axioms sourceMap0055_checked
#print axioms fusedMap0055_checked
#print axioms certified0055
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
