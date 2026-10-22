/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0870 : Family 10 := level10.get ⟨615,by decide⟩
def sourceMap0870 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0870 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0870_checked : acceptsGraphIso
    (source (graph core0870) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2101.graph sourceMap0870=true := by decide +kernel
theorem fusedMap0870_checked : acceptsGraphIso
    (fused (graph core0870) (root 10) 2 2) DegreeTwoThreeSpectrum5305.graph fusedMap0870=true := by decide +kernel
theorem certified0870 : Certified (graph core0870) (root 10) 2 2 :=
  of_native_maps core0870 DegreeOneMiddleResidualSpectrum2101.graph DegreeTwoThreeSpectrum5305.graph
    sourceMap0870 fusedMap0870 sourceMap0870_checked fusedMap0870_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0870
#print axioms sourceMap0870_checked
#print axioms fusedMap0870_checked
#print axioms certified0870
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
