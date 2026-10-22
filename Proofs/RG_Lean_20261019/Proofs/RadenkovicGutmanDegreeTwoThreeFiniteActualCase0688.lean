/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0688 : Family 10 := level10.get ⟨934,by decide⟩
def sourceMap0688 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0688 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0688_checked : acceptsGraphIso
    (source (graph core0688) (root 10) 0 0) DegreeOneSmallSpectrum1399.graph sourceMap0688=true := by decide +kernel
theorem fusedMap0688_checked : acceptsGraphIso
    (fused (graph core0688) (root 10) 0 0) DegreeOneSmallSpectrum1394.graph fusedMap0688=true := by decide +kernel
theorem certified0688 : Certified (graph core0688) (root 10) 0 0 :=
  of_native_maps core0688 DegreeOneSmallSpectrum1399.graph DegreeOneSmallSpectrum1394.graph
    sourceMap0688 fusedMap0688 sourceMap0688_checked fusedMap0688_checked
    DegreeTwoThreeFiniteComparisons.comparison0688
#print axioms sourceMap0688_checked
#print axioms fusedMap0688_checked
#print axioms certified0688
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
