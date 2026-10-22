/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0687 : Family 10 := level10.get ⟨930,by decide⟩
def sourceMap0687 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0687 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0687_checked : acceptsGraphIso
    (source (graph core0687) (root 10) 0 0) DegreeOneSmallSpectrum1190.graph sourceMap0687=true := by decide +kernel
theorem fusedMap0687_checked : acceptsGraphIso
    (fused (graph core0687) (root 10) 0 0) DegreeOneSmallSpectrum1184.graph fusedMap0687=true := by decide +kernel
theorem certified0687 : Certified (graph core0687) (root 10) 0 0 :=
  of_native_maps core0687 DegreeOneSmallSpectrum1190.graph DegreeOneSmallSpectrum1184.graph
    sourceMap0687 fusedMap0687 sourceMap0687_checked fusedMap0687_checked
    DegreeTwoThreeFiniteComparisons.comparison0687
#print axioms sourceMap0687_checked
#print axioms fusedMap0687_checked
#print axioms certified0687
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
