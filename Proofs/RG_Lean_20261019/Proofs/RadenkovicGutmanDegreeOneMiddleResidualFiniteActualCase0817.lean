/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0817 : Family 10 := level10.get ⟨519,by decide⟩
def sourceMap0817 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0817 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0817_checked : acceptsGraphIso
    (source (graph core0817) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2000.graph sourceMap0817=true := by decide +kernel
theorem fusedMap0817_checked : acceptsGraphIso
    (fused (graph core0817) (root 10) 2 2) DegreeTwoThreeSpectrum5162.graph fusedMap0817=true := by decide +kernel
theorem certified0817 : Certified (graph core0817) (root 10) 2 2 :=
  of_native_maps core0817 DegreeOneMiddleResidualSpectrum2000.graph DegreeTwoThreeSpectrum5162.graph
    sourceMap0817 fusedMap0817 sourceMap0817_checked fusedMap0817_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0817
#print axioms sourceMap0817_checked
#print axioms fusedMap0817_checked
#print axioms certified0817
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
