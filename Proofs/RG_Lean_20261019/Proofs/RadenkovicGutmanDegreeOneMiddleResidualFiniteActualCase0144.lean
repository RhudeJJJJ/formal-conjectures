/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0144 : Family 8 := level8.get ⟨137,by decide⟩
def sourceMap0144 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0144 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0144_checked : acceptsGraphIso
    (source (graph core0144) (root 8) 2 2) DegreeOneMiddleResidualSpectrum304.graph sourceMap0144=true := by decide +kernel
theorem fusedMap0144_checked : acceptsGraphIso
    (fused (graph core0144) (root 8) 2 2) DegreeTwoThreeSpectrum2667.graph fusedMap0144=true := by decide +kernel
theorem certified0144 : Certified (graph core0144) (root 8) 2 2 :=
  of_native_maps core0144 DegreeOneMiddleResidualSpectrum304.graph DegreeTwoThreeSpectrum2667.graph
    sourceMap0144 fusedMap0144 sourceMap0144_checked fusedMap0144_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0144
#print axioms sourceMap0144_checked
#print axioms fusedMap0144_checked
#print axioms certified0144
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
