/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0910 : Family 10 := level10.get ⟨1467,by decide⟩
def sourceMap0910 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0910 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0910_checked : acceptsGraphIso
    (source (graph core0910) (root 10) 0 0) DegreeOneSmallSpectrum1224.graph sourceMap0910=true := by decide +kernel
theorem fusedMap0910_checked : acceptsGraphIso
    (fused (graph core0910) (root 10) 0 0) DegreeOneSmallSpectrum1209.graph fusedMap0910=true := by decide +kernel
theorem certified0910 : Certified (graph core0910) (root 10) 0 0 :=
  of_native_maps core0910 DegreeOneSmallSpectrum1224.graph DegreeOneSmallSpectrum1209.graph
    sourceMap0910 fusedMap0910 sourceMap0910_checked fusedMap0910_checked
    DegreeTwoThreeFiniteComparisons.comparison0910
#print axioms sourceMap0910_checked
#print axioms fusedMap0910_checked
#print axioms certified0910
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
