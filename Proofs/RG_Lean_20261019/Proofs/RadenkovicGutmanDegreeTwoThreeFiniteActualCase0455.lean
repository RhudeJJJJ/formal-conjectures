/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0455 : Family 10 := level10.get ⟨249,by decide⟩
def sourceMap0455 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0455 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0455_checked : acceptsGraphIso
    (source (graph core0455) (root 10) 0 0) DegreeOneSmallSpectrum1065.graph sourceMap0455=true := by decide +kernel
theorem fusedMap0455_checked : acceptsGraphIso
    (fused (graph core0455) (root 10) 0 0) DegreeOneSmallSpectrum1222.graph fusedMap0455=true := by decide +kernel
theorem certified0455 : Certified (graph core0455) (root 10) 0 0 :=
  of_native_maps core0455 DegreeOneSmallSpectrum1065.graph DegreeOneSmallSpectrum1222.graph
    sourceMap0455 fusedMap0455 sourceMap0455_checked fusedMap0455_checked
    DegreeTwoThreeFiniteComparisons.comparison0455
#print axioms sourceMap0455_checked
#print axioms fusedMap0455_checked
#print axioms certified0455
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
