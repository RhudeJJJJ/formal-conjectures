/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0724 : Family 10 := level10.get ⟨343,by decide⟩
def sourceMap0724 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0724 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0724_checked : acceptsGraphIso
    (source (graph core0724) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1812.graph sourceMap0724=true := by decide +kernel
theorem fusedMap0724_checked : acceptsGraphIso
    (fused (graph core0724) (root 10) 2 2) DegreeTwoThreeSpectrum5605.graph fusedMap0724=true := by decide +kernel
theorem certified0724 : Certified (graph core0724) (root 10) 2 2 :=
  of_native_maps core0724 DegreeOneMiddleResidualSpectrum1812.graph DegreeTwoThreeSpectrum5605.graph
    sourceMap0724 fusedMap0724 sourceMap0724_checked fusedMap0724_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0724
#print axioms sourceMap0724_checked
#print axioms fusedMap0724_checked
#print axioms certified0724
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
