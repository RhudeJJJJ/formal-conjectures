/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0743 : Family 10 := level10.get ⟨1074,by decide⟩
def sourceMap0743 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0743 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0743_checked : acceptsGraphIso
    (source (graph core0743) (root 10) 0 0) DegreeTwoThreeSpectrum1374.graph sourceMap0743=true := by decide +kernel
theorem fusedMap0743_checked : acceptsGraphIso
    (fused (graph core0743) (root 10) 0 0) DegreeOneSmallSpectrum1689.graph fusedMap0743=true := by decide +kernel
theorem certified0743 : Certified (graph core0743) (root 10) 0 0 :=
  of_native_maps core0743 DegreeTwoThreeSpectrum1374.graph DegreeOneSmallSpectrum1689.graph
    sourceMap0743 fusedMap0743 sourceMap0743_checked fusedMap0743_checked
    DegreeTwoThreeFiniteComparisons.comparison0743
#print axioms sourceMap0743_checked
#print axioms fusedMap0743_checked
#print axioms certified0743
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
