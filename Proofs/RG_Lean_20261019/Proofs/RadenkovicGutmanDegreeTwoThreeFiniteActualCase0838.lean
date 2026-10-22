/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0838 : Family 10 := level10.get ⟨1303,by decide⟩
def sourceMap0838 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0838 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0838_checked : acceptsGraphIso
    (source (graph core0838) (root 10) 0 0) DegreeTwoThreeSpectrum1635.graph sourceMap0838=true := by decide +kernel
theorem fusedMap0838_checked : acceptsGraphIso
    (fused (graph core0838) (root 10) 0 0) DegreeOneSmallSpectrum1918.graph fusedMap0838=true := by decide +kernel
theorem certified0838 : Certified (graph core0838) (root 10) 0 0 :=
  of_native_maps core0838 DegreeTwoThreeSpectrum1635.graph DegreeOneSmallSpectrum1918.graph
    sourceMap0838 fusedMap0838 sourceMap0838_checked fusedMap0838_checked
    DegreeTwoThreeFiniteComparisons.comparison0838
#print axioms sourceMap0838_checked
#print axioms fusedMap0838_checked
#print axioms certified0838
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
