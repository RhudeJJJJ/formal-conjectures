/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0505 : Family 10 := level10.get ⟨23,by decide⟩
def sourceMap0505 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0505 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0505_checked : acceptsGraphIso
    (source (graph core0505) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1361.graph sourceMap0505=true := by decide +kernel
theorem fusedMap0505_checked : acceptsGraphIso
    (fused (graph core0505) (root 10) 2 2) DegreeTwoThreeSpectrum5042.graph fusedMap0505=true := by decide +kernel
theorem certified0505 : Certified (graph core0505) (root 10) 2 2 :=
  of_native_maps core0505 DegreeOneMiddleResidualSpectrum1361.graph DegreeTwoThreeSpectrum5042.graph
    sourceMap0505 fusedMap0505 sourceMap0505_checked fusedMap0505_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0505
#print axioms sourceMap0505_checked
#print axioms fusedMap0505_checked
#print axioms certified0505
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
