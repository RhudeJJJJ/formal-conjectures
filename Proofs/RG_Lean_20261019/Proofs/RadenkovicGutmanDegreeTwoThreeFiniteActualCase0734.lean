/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0734 : Family 10 := level10.get ⟨1050,by decide⟩
def sourceMap0734 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0734 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0734_checked : acceptsGraphIso
    (source (graph core0734) (root 10) 0 0) DegreeTwoThreeSpectrum1405.graph sourceMap0734=true := by decide +kernel
theorem fusedMap0734_checked : acceptsGraphIso
    (fused (graph core0734) (root 10) 0 0) DegreeOneSmallSpectrum1652.graph fusedMap0734=true := by decide +kernel
theorem certified0734 : Certified (graph core0734) (root 10) 0 0 :=
  of_native_maps core0734 DegreeTwoThreeSpectrum1405.graph DegreeOneSmallSpectrum1652.graph
    sourceMap0734 fusedMap0734 sourceMap0734_checked fusedMap0734_checked
    DegreeTwoThreeFiniteComparisons.comparison0734
#print axioms sourceMap0734_checked
#print axioms fusedMap0734_checked
#print axioms certified0734
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
