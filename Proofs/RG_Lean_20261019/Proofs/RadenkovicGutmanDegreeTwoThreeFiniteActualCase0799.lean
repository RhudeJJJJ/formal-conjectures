/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0799 : Family 10 := level10.get ⟨1208,by decide⟩
def sourceMap0799 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0799 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0799_checked : acceptsGraphIso
    (source (graph core0799) (root 10) 0 0) DegreeOneSmallSpectrum1224.graph sourceMap0799=true := by decide +kernel
theorem fusedMap0799_checked : acceptsGraphIso
    (fused (graph core0799) (root 10) 0 0) DegreeOneSmallSpectrum1223.graph fusedMap0799=true := by decide +kernel
theorem certified0799 : Certified (graph core0799) (root 10) 0 0 :=
  of_native_maps core0799 DegreeOneSmallSpectrum1224.graph DegreeOneSmallSpectrum1223.graph
    sourceMap0799 fusedMap0799 sourceMap0799_checked fusedMap0799_checked
    DegreeTwoThreeFiniteComparisons.comparison0799
#print axioms sourceMap0799_checked
#print axioms fusedMap0799_checked
#print axioms certified0799
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
