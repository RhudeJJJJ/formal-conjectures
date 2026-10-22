/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0158 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap0158 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0158 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0158_checked : acceptsGraphIso
    (source (graph core0158) (root 8) 0 0) DegreeOneSmallSpectrum358.graph sourceMap0158=true := by decide +kernel
theorem fusedMap0158_checked : acceptsGraphIso
    (fused (graph core0158) (root 8) 0 0) DegreeOneSmallSpectrum357.graph fusedMap0158=true := by decide +kernel
theorem certified0158 : Certified (graph core0158) (root 8) 0 0 :=
  of_native_maps core0158 DegreeOneSmallSpectrum358.graph DegreeOneSmallSpectrum357.graph
    sourceMap0158 fusedMap0158 sourceMap0158_checked fusedMap0158_checked
    DegreeTwoThreeFiniteComparisons.comparison0158
#print axioms sourceMap0158_checked
#print axioms fusedMap0158_checked
#print axioms certified0158
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
