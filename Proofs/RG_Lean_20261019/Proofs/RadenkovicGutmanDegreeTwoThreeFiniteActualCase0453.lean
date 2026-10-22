/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0453 : Family 10 := level10.get ⟨238,by decide⟩
def sourceMap0453 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0453 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0453_checked : acceptsGraphIso
    (source (graph core0453) (root 10) 0 0) DegreeOneSmallSpectrum1169.graph sourceMap0453=true := by decide +kernel
theorem fusedMap0453_checked : acceptsGraphIso
    (fused (graph core0453) (root 10) 0 0) DegreeOneSmallSpectrum1166.graph fusedMap0453=true := by decide +kernel
theorem certified0453 : Certified (graph core0453) (root 10) 0 0 :=
  of_native_maps core0453 DegreeOneSmallSpectrum1169.graph DegreeOneSmallSpectrum1166.graph
    sourceMap0453 fusedMap0453 sourceMap0453_checked fusedMap0453_checked
    DegreeTwoThreeFiniteComparisons.comparison0453
#print axioms sourceMap0453_checked
#print axioms fusedMap0453_checked
#print axioms certified0453
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
