/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0537 : Family 10 := level10.get ⟨506,by decide⟩
def sourceMap0537 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0537 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0537_checked : acceptsGraphIso
    (source (graph core0537) (root 10) 0 0) DegreeTwoThreeSpectrum1329.graph sourceMap0537=true := by decide +kernel
theorem fusedMap0537_checked : acceptsGraphIso
    (fused (graph core0537) (root 10) 0 0) DegreeOneSmallSpectrum990.graph fusedMap0537=true := by decide +kernel
theorem certified0537 : Certified (graph core0537) (root 10) 0 0 :=
  of_native_maps core0537 DegreeTwoThreeSpectrum1329.graph DegreeOneSmallSpectrum990.graph
    sourceMap0537 fusedMap0537 sourceMap0537_checked fusedMap0537_checked
    DegreeTwoThreeFiniteComparisons.comparison0537
#print axioms sourceMap0537_checked
#print axioms fusedMap0537_checked
#print axioms certified0537
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
