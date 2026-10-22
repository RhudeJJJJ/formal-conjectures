/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0562 : Family 10 := level10.get ⟨587,by decide⟩
def sourceMap0562 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0562 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0562_checked : acceptsGraphIso
    (source (graph core0562) (root 10) 0 0) DegreeOneSmallSpectrum1659.graph sourceMap0562=true := by decide +kernel
theorem fusedMap0562_checked : acceptsGraphIso
    (fused (graph core0562) (root 10) 0 0) DegreeOneSmallSpectrum1130.graph fusedMap0562=true := by decide +kernel
theorem certified0562 : Certified (graph core0562) (root 10) 0 0 :=
  of_native_maps core0562 DegreeOneSmallSpectrum1659.graph DegreeOneSmallSpectrum1130.graph
    sourceMap0562 fusedMap0562 sourceMap0562_checked fusedMap0562_checked
    DegreeTwoThreeFiniteComparisons.comparison0562
#print axioms sourceMap0562_checked
#print axioms fusedMap0562_checked
#print axioms certified0562
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
