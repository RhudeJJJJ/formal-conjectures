/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0845 : Family 10 := level10.get ⟨1322,by decide⟩
def sourceMap0845 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0845 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0845_checked : acceptsGraphIso
    (source (graph core0845) (root 10) 0 0) DegreeOneSmallSpectrum1614.graph sourceMap0845=true := by decide +kernel
theorem fusedMap0845_checked : acceptsGraphIso
    (fused (graph core0845) (root 10) 0 0) DegreeOneSmallSpectrum1947.graph fusedMap0845=true := by decide +kernel
theorem certified0845 : Certified (graph core0845) (root 10) 0 0 :=
  of_native_maps core0845 DegreeOneSmallSpectrum1614.graph DegreeOneSmallSpectrum1947.graph
    sourceMap0845 fusedMap0845 sourceMap0845_checked fusedMap0845_checked
    DegreeTwoThreeFiniteComparisons.comparison0845
#print axioms sourceMap0845_checked
#print axioms fusedMap0845_checked
#print axioms certified0845
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
