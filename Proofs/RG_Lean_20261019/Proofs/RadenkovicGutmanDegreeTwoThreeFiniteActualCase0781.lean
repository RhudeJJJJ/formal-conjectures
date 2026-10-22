/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0781 : Family 10 := level10.get ⟨1166,by decide⟩
def sourceMap0781 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0781 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0781_checked : acceptsGraphIso
    (source (graph core0781) (root 10) 0 0) DegreeOneSmallSpectrum1182.graph sourceMap0781=true := by decide +kernel
theorem fusedMap0781_checked : acceptsGraphIso
    (fused (graph core0781) (root 10) 0 0) DegreeOneSmallSpectrum1181.graph fusedMap0781=true := by decide +kernel
theorem certified0781 : Certified (graph core0781) (root 10) 0 0 :=
  of_native_maps core0781 DegreeOneSmallSpectrum1182.graph DegreeOneSmallSpectrum1181.graph
    sourceMap0781 fusedMap0781 sourceMap0781_checked fusedMap0781_checked
    DegreeTwoThreeFiniteComparisons.comparison0781
#print axioms sourceMap0781_checked
#print axioms fusedMap0781_checked
#print axioms certified0781
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
