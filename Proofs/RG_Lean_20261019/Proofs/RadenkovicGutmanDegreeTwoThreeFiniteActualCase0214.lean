/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0214 : Family 9 := level9.get ⟨207,by decide⟩
def sourceMap0214 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0214 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0214_checked : acceptsGraphIso
    (source (graph core0214) (root 9) 0 0) DegreeOneSmallSpectrum666.graph sourceMap0214=true := by decide +kernel
theorem fusedMap0214_checked : acceptsGraphIso
    (fused (graph core0214) (root 9) 0 0) DegreeOneSmallSpectrum508.graph fusedMap0214=true := by decide +kernel
theorem certified0214 : Certified (graph core0214) (root 9) 0 0 :=
  of_native_maps core0214 DegreeOneSmallSpectrum666.graph DegreeOneSmallSpectrum508.graph
    sourceMap0214 fusedMap0214 sourceMap0214_checked fusedMap0214_checked
    DegreeTwoThreeFiniteComparisons.comparison0214
#print axioms sourceMap0214_checked
#print axioms fusedMap0214_checked
#print axioms certified0214
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
