/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0773 : Family 10 := level10.get ⟨1149,by decide⟩
def sourceMap0773 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0773 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0773_checked : acceptsGraphIso
    (source (graph core0773) (root 10) 0 0) DegreeOneSmallSpectrum1834.graph sourceMap0773=true := by decide +kernel
theorem fusedMap0773_checked : acceptsGraphIso
    (fused (graph core0773) (root 10) 0 0) DegreeOneSmallSpectrum1829.graph fusedMap0773=true := by decide +kernel
theorem certified0773 : Certified (graph core0773) (root 10) 0 0 :=
  of_native_maps core0773 DegreeOneSmallSpectrum1834.graph DegreeOneSmallSpectrum1829.graph
    sourceMap0773 fusedMap0773 sourceMap0773_checked fusedMap0773_checked
    DegreeTwoThreeFiniteComparisons.comparison0773
#print axioms sourceMap0773_checked
#print axioms fusedMap0773_checked
#print axioms certified0773
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
