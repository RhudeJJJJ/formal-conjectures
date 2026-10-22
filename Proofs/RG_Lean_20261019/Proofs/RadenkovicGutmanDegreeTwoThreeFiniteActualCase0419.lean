/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0419 : Family 10 := level10.get ⟨113,by decide⟩
def sourceMap0419 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0419 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0419_checked : acceptsGraphIso
    (source (graph core0419) (root 10) 0 0) DegreeOneSmallSpectrum1055.graph sourceMap0419=true := by decide +kernel
theorem fusedMap0419_checked : acceptsGraphIso
    (fused (graph core0419) (root 10) 0 0) DegreeOneSmallSpectrum932.graph fusedMap0419=true := by decide +kernel
theorem certified0419 : Certified (graph core0419) (root 10) 0 0 :=
  of_native_maps core0419 DegreeOneSmallSpectrum1055.graph DegreeOneSmallSpectrum932.graph
    sourceMap0419 fusedMap0419 sourceMap0419_checked fusedMap0419_checked
    DegreeTwoThreeFiniteComparisons.comparison0419
#print axioms sourceMap0419_checked
#print axioms fusedMap0419_checked
#print axioms certified0419
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
