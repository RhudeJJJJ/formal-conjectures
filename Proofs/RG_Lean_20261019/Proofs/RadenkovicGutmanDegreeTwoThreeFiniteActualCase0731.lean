/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0731 : Family 10 := level10.get ⟨1042,by decide⟩
def sourceMap0731 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0731 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0731_checked : acceptsGraphIso
    (source (graph core0731) (root 10) 0 0) DegreeTwoThreeSpectrum1381.graph sourceMap0731=true := by decide +kernel
theorem fusedMap0731_checked : acceptsGraphIso
    (fused (graph core0731) (root 10) 0 0) DegreeOneSmallSpectrum1635.graph fusedMap0731=true := by decide +kernel
theorem certified0731 : Certified (graph core0731) (root 10) 0 0 :=
  of_native_maps core0731 DegreeTwoThreeSpectrum1381.graph DegreeOneSmallSpectrum1635.graph
    sourceMap0731 fusedMap0731 sourceMap0731_checked fusedMap0731_checked
    DegreeTwoThreeFiniteComparisons.comparison0731
#print axioms sourceMap0731_checked
#print axioms fusedMap0731_checked
#print axioms certified0731
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
