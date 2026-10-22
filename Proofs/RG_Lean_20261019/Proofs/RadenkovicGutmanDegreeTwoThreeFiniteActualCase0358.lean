/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0358 : Family 9 := level9.get ⟨574,by decide⟩
def sourceMap0358 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0358 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0358_checked : acceptsGraphIso
    (source (graph core0358) (root 9) 0 0) DegreeOneSmallSpectrum651.graph sourceMap0358=true := by decide +kernel
theorem fusedMap0358_checked : acceptsGraphIso
    (fused (graph core0358) (root 9) 0 0) DegreeOneSmallSpectrum650.graph fusedMap0358=true := by decide +kernel
theorem certified0358 : Certified (graph core0358) (root 9) 0 0 :=
  of_native_maps core0358 DegreeOneSmallSpectrum651.graph DegreeOneSmallSpectrum650.graph
    sourceMap0358 fusedMap0358 sourceMap0358_checked fusedMap0358_checked
    DegreeTwoThreeFiniteComparisons.comparison0358
#print axioms sourceMap0358_checked
#print axioms fusedMap0358_checked
#print axioms certified0358
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
