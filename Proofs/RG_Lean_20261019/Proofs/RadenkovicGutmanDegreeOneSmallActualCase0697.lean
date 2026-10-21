/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0697 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0697 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0697 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0697_checked : acceptsGraphIso
    (source (graph core0697) (root 7) 1 1) DegreeOneSmallSpectrum680.graph sourceMap0697=true := by decide +kernel
theorem fusedMap0697_checked : acceptsGraphIso
    (fused (graph core0697) (root 7) 1 1) DegreeOneSmallSpectrum428.graph fusedMap0697=true := by decide +kernel
theorem certified0697 : Certified (graph core0697) (root 7) 1 1 :=
  of_native_maps core0697 DegreeOneSmallSpectrum680.graph DegreeOneSmallSpectrum428.graph
    sourceMap0697 fusedMap0697 sourceMap0697_checked fusedMap0697_checked
    DegreeOneSmallComparisons.comparison0697
#print axioms sourceMap0697_checked
#print axioms fusedMap0697_checked
#print axioms certified0697
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
