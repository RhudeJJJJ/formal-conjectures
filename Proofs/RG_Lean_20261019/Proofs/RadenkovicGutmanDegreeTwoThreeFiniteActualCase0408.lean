/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0408 : Family 10 := level10.get ⟨59,by decide⟩
def sourceMap0408 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0408 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0408_checked : acceptsGraphIso
    (source (graph core0408) (root 10) 0 0) DegreeTwoThreeSpectrum902.graph sourceMap0408=true := by decide +kernel
theorem fusedMap0408_checked : acceptsGraphIso
    (fused (graph core0408) (root 10) 0 0) DegreeOneSmallSpectrum867.graph fusedMap0408=true := by decide +kernel
theorem certified0408 : Certified (graph core0408) (root 10) 0 0 :=
  of_native_maps core0408 DegreeTwoThreeSpectrum902.graph DegreeOneSmallSpectrum867.graph
    sourceMap0408 fusedMap0408 sourceMap0408_checked fusedMap0408_checked
    DegreeTwoThreeFiniteComparisons.comparison0408
#print axioms sourceMap0408_checked
#print axioms fusedMap0408_checked
#print axioms certified0408
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
