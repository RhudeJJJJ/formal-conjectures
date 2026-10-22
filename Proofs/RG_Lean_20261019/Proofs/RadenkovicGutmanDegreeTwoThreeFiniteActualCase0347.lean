/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0347 : Family 9 := level9.get ⟨552,by decide⟩
def sourceMap0347 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 9 0 0 v)
def fusedMap0347 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0347_checked : acceptsGraphIso
    (source (graph core0347) (root 9) 0 0) DegreeTwoThreeSpectrum710.graph sourceMap0347=true := by decide +kernel
theorem fusedMap0347_checked : acceptsGraphIso
    (fused (graph core0347) (root 9) 0 0) DegreeOneSmallSpectrum607.graph fusedMap0347=true := by decide +kernel
theorem certified0347 : Certified (graph core0347) (root 9) 0 0 :=
  of_native_maps core0347 DegreeTwoThreeSpectrum710.graph DegreeOneSmallSpectrum607.graph
    sourceMap0347 fusedMap0347 sourceMap0347_checked fusedMap0347_checked
    DegreeTwoThreeFiniteComparisons.comparison0347
#print axioms sourceMap0347_checked
#print axioms fusedMap0347_checked
#print axioms certified0347
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
