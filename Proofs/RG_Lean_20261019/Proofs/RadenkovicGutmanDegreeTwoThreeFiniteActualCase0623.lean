/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0623 : Family 10 := level10.get ⟨759,by decide⟩
def sourceMap0623 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0623 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0623_checked : acceptsGraphIso
    (source (graph core0623) (root 10) 0 0) DegreeOneSmallSpectrum1390.graph sourceMap0623=true := by decide +kernel
theorem fusedMap0623_checked : acceptsGraphIso
    (fused (graph core0623) (root 10) 0 0) DegreeOneSmallSpectrum1388.graph fusedMap0623=true := by decide +kernel
theorem certified0623 : Certified (graph core0623) (root 10) 0 0 :=
  of_native_maps core0623 DegreeOneSmallSpectrum1390.graph DegreeOneSmallSpectrum1388.graph
    sourceMap0623 fusedMap0623 sourceMap0623_checked fusedMap0623_checked
    DegreeTwoThreeFiniteComparisons.comparison0623
#print axioms sourceMap0623_checked
#print axioms fusedMap0623_checked
#print axioms certified0623
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
