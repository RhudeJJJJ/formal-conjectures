/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0166 : Family 9 := level9.get ⟨40,by decide⟩
def sourceMap0166 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,7,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0166 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0166_checked : acceptsGraphIso
    (source (graph core0166) (root 9) 0 0) DegreeOneSmallSpectrum411.graph sourceMap0166=true := by decide +kernel
theorem fusedMap0166_checked : acceptsGraphIso
    (fused (graph core0166) (root 9) 0 0) DegreeOneSmallSpectrum381.graph fusedMap0166=true := by decide +kernel
theorem certified0166 : Certified (graph core0166) (root 9) 0 0 :=
  of_native_maps core0166 DegreeOneSmallSpectrum411.graph DegreeOneSmallSpectrum381.graph
    sourceMap0166 fusedMap0166 sourceMap0166_checked fusedMap0166_checked
    DegreeTwoThreeFiniteComparisons.comparison0166
#print axioms sourceMap0166_checked
#print axioms fusedMap0166_checked
#print axioms certified0166
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
