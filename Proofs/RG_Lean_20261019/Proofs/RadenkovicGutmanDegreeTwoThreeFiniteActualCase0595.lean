/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0595 : Family 10 := level10.get ⟨675,by decide⟩
def sourceMap0595 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0595 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0595_checked : acceptsGraphIso
    (source (graph core0595) (root 10) 0 0) DegreeOneSmallSpectrum1218.graph sourceMap0595=true := by decide +kernel
theorem fusedMap0595_checked : acceptsGraphIso
    (fused (graph core0595) (root 10) 0 0) DegreeOneSmallSpectrum1203.graph fusedMap0595=true := by decide +kernel
theorem certified0595 : Certified (graph core0595) (root 10) 0 0 :=
  of_native_maps core0595 DegreeOneSmallSpectrum1218.graph DegreeOneSmallSpectrum1203.graph
    sourceMap0595 fusedMap0595 sourceMap0595_checked fusedMap0595_checked
    DegreeTwoThreeFiniteComparisons.comparison0595
#print axioms sourceMap0595_checked
#print axioms fusedMap0595_checked
#print axioms certified0595
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
