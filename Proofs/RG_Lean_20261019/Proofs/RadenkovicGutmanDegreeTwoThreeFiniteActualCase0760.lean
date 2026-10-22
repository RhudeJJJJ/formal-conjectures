/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0760 : Family 10 := level10.get ⟨1117,by decide⟩
def sourceMap0760 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0760 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0760_checked : acceptsGraphIso
    (source (graph core0760) (root 10) 0 0) DegreeOneSmallSpectrum1630.graph sourceMap0760=true := by decide +kernel
theorem fusedMap0760_checked : acceptsGraphIso
    (fused (graph core0760) (root 10) 0 0) DegreeOneSmallSpectrum1768.graph fusedMap0760=true := by decide +kernel
theorem certified0760 : Certified (graph core0760) (root 10) 0 0 :=
  of_native_maps core0760 DegreeOneSmallSpectrum1630.graph DegreeOneSmallSpectrum1768.graph
    sourceMap0760 fusedMap0760 sourceMap0760_checked fusedMap0760_checked
    DegreeTwoThreeFiniteComparisons.comparison0760
#print axioms sourceMap0760_checked
#print axioms fusedMap0760_checked
#print axioms certified0760
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
