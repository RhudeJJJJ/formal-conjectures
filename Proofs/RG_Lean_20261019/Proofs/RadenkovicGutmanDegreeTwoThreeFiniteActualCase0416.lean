/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0416 : Family 10 := level10.get ⟨98,by decide⟩
def sourceMap0416 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0416 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0416_checked : acceptsGraphIso
    (source (graph core0416) (root 10) 0 0) DegreeTwoThreeSpectrum916.graph sourceMap0416=true := by decide +kernel
theorem fusedMap0416_checked : acceptsGraphIso
    (fused (graph core0416) (root 10) 0 0) DegreeOneSmallSpectrum919.graph fusedMap0416=true := by decide +kernel
theorem certified0416 : Certified (graph core0416) (root 10) 0 0 :=
  of_native_maps core0416 DegreeTwoThreeSpectrum916.graph DegreeOneSmallSpectrum919.graph
    sourceMap0416 fusedMap0416 sourceMap0416_checked fusedMap0416_checked
    DegreeTwoThreeFiniteComparisons.comparison0416
#print axioms sourceMap0416_checked
#print axioms fusedMap0416_checked
#print axioms certified0416
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
