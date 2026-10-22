/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0735 : Family 10 := level10.get ⟨1051,by decide⟩
def sourceMap0735 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0735 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0735_checked : acceptsGraphIso
    (source (graph core0735) (root 10) 0 0) DegreeTwoThreeSpectrum1414.graph sourceMap0735=true := by decide +kernel
theorem fusedMap0735_checked : acceptsGraphIso
    (fused (graph core0735) (root 10) 0 0) DegreeOneSmallSpectrum1651.graph fusedMap0735=true := by decide +kernel
theorem certified0735 : Certified (graph core0735) (root 10) 0 0 :=
  of_native_maps core0735 DegreeTwoThreeSpectrum1414.graph DegreeOneSmallSpectrum1651.graph
    sourceMap0735 fusedMap0735 sourceMap0735_checked fusedMap0735_checked
    DegreeTwoThreeFiniteComparisons.comparison0735
#print axioms sourceMap0735_checked
#print axioms fusedMap0735_checked
#print axioms certified0735
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
