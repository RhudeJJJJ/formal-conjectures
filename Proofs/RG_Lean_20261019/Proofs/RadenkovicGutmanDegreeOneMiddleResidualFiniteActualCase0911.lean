/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0911 : Family 10 := level10.get ⟨701,by decide⟩
def sourceMap0911 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0911 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0911_checked : acceptsGraphIso
    (source (graph core0911) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2171.graph sourceMap0911=true := by decide +kernel
theorem fusedMap0911_checked : acceptsGraphIso
    (fused (graph core0911) (root 10) 2 2) DegreeTwoThreeSpectrum5442.graph fusedMap0911=true := by decide +kernel
theorem certified0911 : Certified (graph core0911) (root 10) 2 2 :=
  of_native_maps core0911 DegreeOneMiddleResidualSpectrum2171.graph DegreeTwoThreeSpectrum5442.graph
    sourceMap0911 fusedMap0911 sourceMap0911_checked fusedMap0911_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0911
#print axioms sourceMap0911_checked
#print axioms fusedMap0911_checked
#print axioms certified0911
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
