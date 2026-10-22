/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0282 : Family 9 := level9.get ⟨395,by decide⟩
def sourceMap0282 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0282 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0282_checked : acceptsGraphIso
    (source (graph core0282) (root 9) 0 0) DegreeOneSmallSpectrum633.graph sourceMap0282=true := by decide +kernel
theorem fusedMap0282_checked : acceptsGraphIso
    (fused (graph core0282) (root 9) 0 0) DegreeOneSmallSpectrum763.graph fusedMap0282=true := by decide +kernel
theorem certified0282 : Certified (graph core0282) (root 9) 0 0 :=
  of_native_maps core0282 DegreeOneSmallSpectrum633.graph DegreeOneSmallSpectrum763.graph
    sourceMap0282 fusedMap0282 sourceMap0282_checked fusedMap0282_checked
    DegreeTwoThreeFiniteComparisons.comparison0282
#print axioms sourceMap0282_checked
#print axioms fusedMap0282_checked
#print axioms certified0282
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
