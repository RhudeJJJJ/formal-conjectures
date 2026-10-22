/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0437 : Family 10 := level10.get ⟨180,by decide⟩
def sourceMap0437 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,7,8,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0437 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0437_checked : acceptsGraphIso
    (source (graph core0437) (root 10) 0 0) DegreeOneSmallSpectrum1015.graph sourceMap0437=true := by decide +kernel
theorem fusedMap0437_checked : acceptsGraphIso
    (fused (graph core0437) (root 10) 0 0) DegreeOneSmallSpectrum923.graph fusedMap0437=true := by decide +kernel
theorem certified0437 : Certified (graph core0437) (root 10) 0 0 :=
  of_native_maps core0437 DegreeOneSmallSpectrum1015.graph DegreeOneSmallSpectrum923.graph
    sourceMap0437 fusedMap0437 sourceMap0437_checked fusedMap0437_checked
    DegreeTwoThreeFiniteComparisons.comparison0437
#print axioms sourceMap0437_checked
#print axioms fusedMap0437_checked
#print axioms certified0437
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
