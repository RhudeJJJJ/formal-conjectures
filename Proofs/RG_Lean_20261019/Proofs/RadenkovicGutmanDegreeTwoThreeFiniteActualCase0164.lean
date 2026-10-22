/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0164 : Family 9 := level9.get ⟨33,by decide⟩
def sourceMap0164 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0164 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0164_checked : acceptsGraphIso
    (source (graph core0164) (root 9) 0 0) DegreeOneSmallSpectrum427.graph sourceMap0164=true := by decide +kernel
theorem fusedMap0164_checked : acceptsGraphIso
    (fused (graph core0164) (root 9) 0 0) DegreeOneSmallSpectrum385.graph fusedMap0164=true := by decide +kernel
theorem certified0164 : Certified (graph core0164) (root 9) 0 0 :=
  of_native_maps core0164 DegreeOneSmallSpectrum427.graph DegreeOneSmallSpectrum385.graph
    sourceMap0164 fusedMap0164 sourceMap0164_checked fusedMap0164_checked
    DegreeTwoThreeFiniteComparisons.comparison0164
#print axioms sourceMap0164_checked
#print axioms fusedMap0164_checked
#print axioms certified0164
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
