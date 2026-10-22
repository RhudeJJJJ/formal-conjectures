/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0865 : Family 10 := level10.get ⟨599,by decide⟩
def sourceMap0865 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0865 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0865_checked : acceptsGraphIso
    (source (graph core0865) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2095.graph sourceMap0865=true := by decide +kernel
theorem fusedMap0865_checked : acceptsGraphIso
    (fused (graph core0865) (root 10) 2 2) DegreeTwoThreeSpectrum5274.graph fusedMap0865=true := by decide +kernel
theorem certified0865 : Certified (graph core0865) (root 10) 2 2 :=
  of_native_maps core0865 DegreeOneMiddleResidualSpectrum2095.graph DegreeTwoThreeSpectrum5274.graph
    sourceMap0865 fusedMap0865 sourceMap0865_checked fusedMap0865_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0865
#print axioms sourceMap0865_checked
#print axioms fusedMap0865_checked
#print axioms certified0865
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
