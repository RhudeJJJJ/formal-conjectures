/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0505 : Family 10 := level10.get ⟨414,by decide⟩
def sourceMap0505 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0505 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0505_checked : acceptsGraphIso
    (source (graph core0505) (root 10) 0 0) DegreeOneSmallSpectrum1391.graph sourceMap0505=true := by decide +kernel
theorem fusedMap0505_checked : acceptsGraphIso
    (fused (graph core0505) (root 10) 0 0) DegreeOneSmallSpectrum1346.graph fusedMap0505=true := by decide +kernel
theorem certified0505 : Certified (graph core0505) (root 10) 0 0 :=
  of_native_maps core0505 DegreeOneSmallSpectrum1391.graph DegreeOneSmallSpectrum1346.graph
    sourceMap0505 fusedMap0505 sourceMap0505_checked fusedMap0505_checked
    DegreeTwoThreeFiniteComparisons.comparison0505
#print axioms sourceMap0505_checked
#print axioms fusedMap0505_checked
#print axioms certified0505
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
