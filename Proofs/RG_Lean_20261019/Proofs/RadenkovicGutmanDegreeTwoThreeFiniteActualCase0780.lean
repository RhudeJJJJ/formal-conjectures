/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0780 : Family 10 := level10.get ⟨1163,by decide⟩
def sourceMap0780 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0780 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0780_checked : acceptsGraphIso
    (source (graph core0780) (root 10) 0 0) DegreeOneSmallSpectrum1795.graph sourceMap0780=true := by decide +kernel
theorem fusedMap0780_checked : acceptsGraphIso
    (fused (graph core0780) (root 10) 0 0) DegreeOneSmallSpectrum1758.graph fusedMap0780=true := by decide +kernel
theorem certified0780 : Certified (graph core0780) (root 10) 0 0 :=
  of_native_maps core0780 DegreeOneSmallSpectrum1795.graph DegreeOneSmallSpectrum1758.graph
    sourceMap0780 fusedMap0780 sourceMap0780_checked fusedMap0780_checked
    DegreeTwoThreeFiniteComparisons.comparison0780
#print axioms sourceMap0780_checked
#print axioms fusedMap0780_checked
#print axioms certified0780
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
