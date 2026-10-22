/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0797 : Family 10 := level10.get ⟨1205,by decide⟩
def sourceMap0797 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0797 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0797_checked : acceptsGraphIso
    (source (graph core0797) (root 10) 0 0) DegreeOneSmallSpectrum1639.graph sourceMap0797=true := by decide +kernel
theorem fusedMap0797_checked : acceptsGraphIso
    (fused (graph core0797) (root 10) 0 0) DegreeOneSmallSpectrum1875.graph fusedMap0797=true := by decide +kernel
theorem certified0797 : Certified (graph core0797) (root 10) 0 0 :=
  of_native_maps core0797 DegreeOneSmallSpectrum1639.graph DegreeOneSmallSpectrum1875.graph
    sourceMap0797 fusedMap0797 sourceMap0797_checked fusedMap0797_checked
    DegreeTwoThreeFiniteComparisons.comparison0797
#print axioms sourceMap0797_checked
#print axioms fusedMap0797_checked
#print axioms certified0797
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
