/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0497 : Family 10 := level10.get ⟨388,by decide⟩
def sourceMap0497 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0497 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0497_checked : acceptsGraphIso
    (source (graph core0497) (root 10) 0 0) DegreeOneSmallSpectrum1388.graph sourceMap0497=true := by decide +kernel
theorem fusedMap0497_checked : acceptsGraphIso
    (fused (graph core0497) (root 10) 0 0) DegreeOneSmallSpectrum1343.graph fusedMap0497=true := by decide +kernel
theorem certified0497 : Certified (graph core0497) (root 10) 0 0 :=
  of_native_maps core0497 DegreeOneSmallSpectrum1388.graph DegreeOneSmallSpectrum1343.graph
    sourceMap0497 fusedMap0497 sourceMap0497_checked fusedMap0497_checked
    DegreeTwoThreeFiniteComparisons.comparison0497
#print axioms sourceMap0497_checked
#print axioms fusedMap0497_checked
#print axioms certified0497
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
