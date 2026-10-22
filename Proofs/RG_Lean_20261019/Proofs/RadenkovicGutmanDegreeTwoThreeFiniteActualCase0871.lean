/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0871 : Family 10 := level10.get ⟨1378,by decide⟩
def sourceMap0871 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0871 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0871_checked : acceptsGraphIso
    (source (graph core0871) (root 10) 0 0) DegreeOneSmallSpectrum1435.graph sourceMap0871=true := by decide +kernel
theorem fusedMap0871_checked : acceptsGraphIso
    (fused (graph core0871) (root 10) 0 0) DegreeOneSmallSpectrum1434.graph fusedMap0871=true := by decide +kernel
theorem certified0871 : Certified (graph core0871) (root 10) 0 0 :=
  of_native_maps core0871 DegreeOneSmallSpectrum1435.graph DegreeOneSmallSpectrum1434.graph
    sourceMap0871 fusedMap0871 sourceMap0871_checked fusedMap0871_checked
    DegreeTwoThreeFiniteComparisons.comparison0871
#print axioms sourceMap0871_checked
#print axioms fusedMap0871_checked
#print axioms certified0871
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
