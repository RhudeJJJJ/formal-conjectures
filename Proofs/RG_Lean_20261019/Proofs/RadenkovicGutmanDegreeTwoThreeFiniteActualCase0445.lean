/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0445 : Family 10 := level10.get ⟨209,by decide⟩
def sourceMap0445 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0445 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0445_checked : acceptsGraphIso
    (source (graph core0445) (root 10) 0 0) DegreeTwoThreeSpectrum890.graph sourceMap0445=true := by decide +kernel
theorem fusedMap0445_checked : acceptsGraphIso
    (fused (graph core0445) (root 10) 0 0) DegreeOneSmallSpectrum1073.graph fusedMap0445=true := by decide +kernel
theorem certified0445 : Certified (graph core0445) (root 10) 0 0 :=
  of_native_maps core0445 DegreeTwoThreeSpectrum890.graph DegreeOneSmallSpectrum1073.graph
    sourceMap0445 fusedMap0445 sourceMap0445_checked fusedMap0445_checked
    DegreeTwoThreeFiniteComparisons.comparison0445
#print axioms sourceMap0445_checked
#print axioms fusedMap0445_checked
#print axioms certified0445
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
