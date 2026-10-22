/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0737 : Family 10 := level10.get ⟨1058,by decide⟩
def sourceMap0737 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0737 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0737_checked : acceptsGraphIso
    (source (graph core0737) (root 10) 0 0) DegreeTwoThreeSpectrum1405.graph sourceMap0737=true := by decide +kernel
theorem fusedMap0737_checked : acceptsGraphIso
    (fused (graph core0737) (root 10) 0 0) DegreeOneSmallSpectrum1665.graph fusedMap0737=true := by decide +kernel
theorem certified0737 : Certified (graph core0737) (root 10) 0 0 :=
  of_native_maps core0737 DegreeTwoThreeSpectrum1405.graph DegreeOneSmallSpectrum1665.graph
    sourceMap0737 fusedMap0737 sourceMap0737_checked fusedMap0737_checked
    DegreeTwoThreeFiniteComparisons.comparison0737
#print axioms sourceMap0737_checked
#print axioms fusedMap0737_checked
#print axioms certified0737
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
