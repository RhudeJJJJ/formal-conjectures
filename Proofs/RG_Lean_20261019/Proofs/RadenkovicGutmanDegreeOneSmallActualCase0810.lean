/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0810 : Family 8 := level8.get ⟨21,by decide⟩
def sourceMap0810 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0810 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0810_checked : acceptsGraphIso
    (source (graph core0810) (root 8) 1 1) DegreeOneSmallSpectrum1345.graph sourceMap0810=true := by decide +kernel
theorem fusedMap0810_checked : acceptsGraphIso
    (fused (graph core0810) (root 8) 1 1) DegreeOneSmallSpectrum956.graph fusedMap0810=true := by decide +kernel
theorem certified0810 : Certified (graph core0810) (root 8) 1 1 :=
  of_native_maps core0810 DegreeOneSmallSpectrum1345.graph DegreeOneSmallSpectrum956.graph
    sourceMap0810 fusedMap0810 sourceMap0810_checked fusedMap0810_checked
    DegreeOneSmallComparisons.comparison0810
#print axioms sourceMap0810_checked
#print axioms fusedMap0810_checked
#print axioms certified0810
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
