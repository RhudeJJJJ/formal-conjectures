/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0487 : Family 10 := level10.get ⟨3,by decide⟩
def sourceMap0487 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,10,11,12,13,14,15,16,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0487 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0487_checked : acceptsGraphIso
    (source (graph core0487) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1384.graph sourceMap0487=true := by decide +kernel
theorem fusedMap0487_checked : acceptsGraphIso
    (fused (graph core0487) (root 10) 2 2) DegreeTwoThreeSpectrum4961.graph fusedMap0487=true := by decide +kernel
theorem certified0487 : Certified (graph core0487) (root 10) 2 2 :=
  of_native_maps core0487 DegreeOneMiddleResidualSpectrum1384.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap0487 fusedMap0487 sourceMap0487_checked fusedMap0487_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0487
#print axioms sourceMap0487_checked
#print axioms fusedMap0487_checked
#print axioms certified0487
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
