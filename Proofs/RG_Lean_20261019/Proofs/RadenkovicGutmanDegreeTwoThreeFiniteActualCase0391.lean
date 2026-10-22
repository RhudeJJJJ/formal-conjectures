/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0391 : Family 9 := level9.get ⟨657,by decide⟩
def sourceMap0391 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0391 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0391_checked : acceptsGraphIso
    (source (graph core0391) (root 9) 0 0) DegreeOneSmallSpectrum807.graph sourceMap0391=true := by decide +kernel
theorem fusedMap0391_checked : acceptsGraphIso
    (fused (graph core0391) (root 9) 0 0) DegreeOneSmallSpectrum806.graph fusedMap0391=true := by decide +kernel
theorem certified0391 : Certified (graph core0391) (root 9) 0 0 :=
  of_native_maps core0391 DegreeOneSmallSpectrum807.graph DegreeOneSmallSpectrum806.graph
    sourceMap0391 fusedMap0391 sourceMap0391_checked fusedMap0391_checked
    DegreeTwoThreeFiniteComparisons.comparison0391
#print axioms sourceMap0391_checked
#print axioms fusedMap0391_checked
#print axioms certified0391
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
