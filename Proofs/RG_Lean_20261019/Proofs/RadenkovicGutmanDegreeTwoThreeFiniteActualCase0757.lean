/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0757 : Family 10 := level10.get ⟨1108,by decide⟩
def sourceMap0757 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0757 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0757_checked : acceptsGraphIso
    (source (graph core0757) (root 10) 0 0) DegreeOneSmallSpectrum1673.graph sourceMap0757=true := by decide +kernel
theorem fusedMap0757_checked : acceptsGraphIso
    (fused (graph core0757) (root 10) 0 0) DegreeOneSmallSpectrum1742.graph fusedMap0757=true := by decide +kernel
theorem certified0757 : Certified (graph core0757) (root 10) 0 0 :=
  of_native_maps core0757 DegreeOneSmallSpectrum1673.graph DegreeOneSmallSpectrum1742.graph
    sourceMap0757 fusedMap0757 sourceMap0757_checked fusedMap0757_checked
    DegreeTwoThreeFiniteComparisons.comparison0757
#print axioms sourceMap0757_checked
#print axioms fusedMap0757_checked
#print axioms certified0757
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
