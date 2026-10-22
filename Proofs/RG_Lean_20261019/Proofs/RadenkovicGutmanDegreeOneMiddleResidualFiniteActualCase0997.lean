/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0997 : Family 10 := level10.get ⟨883,by decide⟩
def sourceMap0997 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0997 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0997_checked : acceptsGraphIso
    (source (graph core0997) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2300.graph sourceMap0997=true := by decide +kernel
theorem fusedMap0997_checked : acceptsGraphIso
    (fused (graph core0997) (root 10) 2 2) DegreeTwoThreeSpectrum5737.graph fusedMap0997=true := by decide +kernel
theorem certified0997 : Certified (graph core0997) (root 10) 2 2 :=
  of_native_maps core0997 DegreeOneMiddleResidualSpectrum2300.graph DegreeTwoThreeSpectrum5737.graph
    sourceMap0997 fusedMap0997 sourceMap0997_checked fusedMap0997_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0997
#print axioms sourceMap0997_checked
#print axioms fusedMap0997_checked
#print axioms certified0997
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
