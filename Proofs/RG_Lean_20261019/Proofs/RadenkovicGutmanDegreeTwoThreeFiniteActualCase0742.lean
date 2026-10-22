/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0742 : Family 10 := level10.get ⟨1071,by decide⟩
def sourceMap0742 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0742 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0742_checked : acceptsGraphIso
    (source (graph core0742) (root 10) 0 0) DegreeOneSmallSpectrum1610.graph sourceMap0742=true := by decide +kernel
theorem fusedMap0742_checked : acceptsGraphIso
    (fused (graph core0742) (root 10) 0 0) DegreeOneSmallSpectrum1688.graph fusedMap0742=true := by decide +kernel
theorem certified0742 : Certified (graph core0742) (root 10) 0 0 :=
  of_native_maps core0742 DegreeOneSmallSpectrum1610.graph DegreeOneSmallSpectrum1688.graph
    sourceMap0742 fusedMap0742 sourceMap0742_checked fusedMap0742_checked
    DegreeTwoThreeFiniteComparisons.comparison0742
#print axioms sourceMap0742_checked
#print axioms fusedMap0742_checked
#print axioms certified0742
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
