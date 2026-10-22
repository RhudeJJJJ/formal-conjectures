/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0820 : Family 10 := level10.get ⟨523,by decide⟩
def sourceMap0820 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0820 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0820_checked : acceptsGraphIso
    (source (graph core0820) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2007.graph sourceMap0820=true := by decide +kernel
theorem fusedMap0820_checked : acceptsGraphIso
    (fused (graph core0820) (root 10) 2 2) DegreeTwoThreeSpectrum5166.graph fusedMap0820=true := by decide +kernel
theorem certified0820 : Certified (graph core0820) (root 10) 2 2 :=
  of_native_maps core0820 DegreeOneMiddleResidualSpectrum2007.graph DegreeTwoThreeSpectrum5166.graph
    sourceMap0820 fusedMap0820 sourceMap0820_checked fusedMap0820_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0820
#print axioms sourceMap0820_checked
#print axioms fusedMap0820_checked
#print axioms certified0820
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
