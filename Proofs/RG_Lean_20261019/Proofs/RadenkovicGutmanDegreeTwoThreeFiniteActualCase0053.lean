/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0053 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap0053 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0053 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap0053_checked : acceptsGraphIso
    (source (graph core0053) (root 7) 0 0) DegreeOneSmallSpectrum113.graph sourceMap0053=true := by decide +kernel
theorem fusedMap0053_checked : acceptsGraphIso
    (fused (graph core0053) (root 7) 0 0) DegreeOneSmallSpectrum109.graph fusedMap0053=true := by decide +kernel
theorem certified0053 : Certified (graph core0053) (root 7) 0 0 :=
  of_native_maps core0053 DegreeOneSmallSpectrum113.graph DegreeOneSmallSpectrum109.graph
    sourceMap0053 fusedMap0053 sourceMap0053_checked fusedMap0053_checked
    DegreeTwoThreeFiniteComparisons.comparison0053
#print axioms sourceMap0053_checked
#print axioms fusedMap0053_checked
#print axioms certified0053
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
