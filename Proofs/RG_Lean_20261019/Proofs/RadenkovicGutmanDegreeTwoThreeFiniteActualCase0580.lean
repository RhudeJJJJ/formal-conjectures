/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0580 : Family 10 := level10.get ⟨639,by decide⟩
def sourceMap0580 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0580 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0580_checked : acceptsGraphIso
    (source (graph core0580) (root 10) 0 0) DegreeOneSmallSpectrum1220.graph sourceMap0580=true := by decide +kernel
theorem fusedMap0580_checked : acceptsGraphIso
    (fused (graph core0580) (root 10) 0 0) DegreeOneSmallSpectrum1219.graph fusedMap0580=true := by decide +kernel
theorem certified0580 : Certified (graph core0580) (root 10) 0 0 :=
  of_native_maps core0580 DegreeOneSmallSpectrum1220.graph DegreeOneSmallSpectrum1219.graph
    sourceMap0580 fusedMap0580 sourceMap0580_checked fusedMap0580_checked
    DegreeTwoThreeFiniteComparisons.comparison0580
#print axioms sourceMap0580_checked
#print axioms fusedMap0580_checked
#print axioms certified0580
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
