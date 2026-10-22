/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0836 : Family 10 := level10.get ⟨549,by decide⟩
def sourceMap0836 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0836 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0836_checked : acceptsGraphIso
    (source (graph core0836) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2035.graph sourceMap0836=true := by decide +kernel
theorem fusedMap0836_checked : acceptsGraphIso
    (fused (graph core0836) (root 10) 2 2) DegreeTwoThreeSpectrum5203.graph fusedMap0836=true := by decide +kernel
theorem certified0836 : Certified (graph core0836) (root 10) 2 2 :=
  of_native_maps core0836 DegreeOneMiddleResidualSpectrum2035.graph DegreeTwoThreeSpectrum5203.graph
    sourceMap0836 fusedMap0836 sourceMap0836_checked fusedMap0836_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0836
#print axioms sourceMap0836_checked
#print axioms fusedMap0836_checked
#print axioms certified0836
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
