/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0868 : Family 10 := level10.get ⟨1372,by decide⟩
def sourceMap0868 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0868 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0868_checked : acceptsGraphIso
    (source (graph core0868) (root 10) 0 0) DegreeOneSmallSpectrum1949.graph sourceMap0868=true := by decide +kernel
theorem fusedMap0868_checked : acceptsGraphIso
    (fused (graph core0868) (root 10) 0 0) DegreeOneSmallSpectrum1925.graph fusedMap0868=true := by decide +kernel
theorem certified0868 : Certified (graph core0868) (root 10) 0 0 :=
  of_native_maps core0868 DegreeOneSmallSpectrum1949.graph DegreeOneSmallSpectrum1925.graph
    sourceMap0868 fusedMap0868 sourceMap0868_checked fusedMap0868_checked
    DegreeTwoThreeFiniteComparisons.comparison0868
#print axioms sourceMap0868_checked
#print axioms fusedMap0868_checked
#print axioms certified0868
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
