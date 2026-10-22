/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0191 : Family 9 := level9.get ⟨131,by decide⟩
def sourceMap0191 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,7,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0191 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,7,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0191_checked : acceptsGraphIso
    (source (graph core0191) (root 9) 0 0) DegreeOneSmallSpectrum528.graph sourceMap0191=true := by decide +kernel
theorem fusedMap0191_checked : acceptsGraphIso
    (fused (graph core0191) (root 9) 0 0) DegreeOneSmallSpectrum510.graph fusedMap0191=true := by decide +kernel
theorem certified0191 : Certified (graph core0191) (root 9) 0 0 :=
  of_native_maps core0191 DegreeOneSmallSpectrum528.graph DegreeOneSmallSpectrum510.graph
    sourceMap0191 fusedMap0191 sourceMap0191_checked fusedMap0191_checked
    DegreeTwoThreeFiniteComparisons.comparison0191
#print axioms sourceMap0191_checked
#print axioms fusedMap0191_checked
#print axioms certified0191
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
