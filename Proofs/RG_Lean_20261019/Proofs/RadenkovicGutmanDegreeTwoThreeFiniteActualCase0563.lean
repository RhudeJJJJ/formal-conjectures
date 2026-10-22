/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0563 : Family 10 := level10.get ⟨588,by decide⟩
def sourceMap0563 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0563 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0563_checked : acceptsGraphIso
    (source (graph core0563) (root 10) 0 0) DegreeOneSmallSpectrum1129.graph sourceMap0563=true := by decide +kernel
theorem fusedMap0563_checked : acceptsGraphIso
    (fused (graph core0563) (root 10) 0 0) DegreeOneSmallSpectrum1128.graph fusedMap0563=true := by decide +kernel
theorem certified0563 : Certified (graph core0563) (root 10) 0 0 :=
  of_native_maps core0563 DegreeOneSmallSpectrum1129.graph DegreeOneSmallSpectrum1128.graph
    sourceMap0563 fusedMap0563 sourceMap0563_checked fusedMap0563_checked
    DegreeTwoThreeFiniteComparisons.comparison0563
#print axioms sourceMap0563_checked
#print axioms fusedMap0563_checked
#print axioms certified0563
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
