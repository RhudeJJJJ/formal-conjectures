/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0810 : Family 10 := level10.get ⟨1228,by decide⟩
def sourceMap0810 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0810 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0810_checked : acceptsGraphIso
    (source (graph core0810) (root 10) 0 0) DegreeOneSmallSpectrum1255.graph sourceMap0810=true := by decide +kernel
theorem fusedMap0810_checked : acceptsGraphIso
    (fused (graph core0810) (root 10) 0 0) DegreeOneSmallSpectrum1254.graph fusedMap0810=true := by decide +kernel
theorem certified0810 : Certified (graph core0810) (root 10) 0 0 :=
  of_native_maps core0810 DegreeOneSmallSpectrum1255.graph DegreeOneSmallSpectrum1254.graph
    sourceMap0810 fusedMap0810 sourceMap0810_checked fusedMap0810_checked
    DegreeTwoThreeFiniteComparisons.comparison0810
#print axioms sourceMap0810_checked
#print axioms fusedMap0810_checked
#print axioms certified0810
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
