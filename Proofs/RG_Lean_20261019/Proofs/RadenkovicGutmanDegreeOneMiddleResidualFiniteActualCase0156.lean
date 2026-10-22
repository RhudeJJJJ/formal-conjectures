/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0156 : Family 8 := level8.get ⟨166,by decide⟩
def sourceMap0156 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap0156 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0156_checked : acceptsGraphIso
    (source (graph core0156) (root 8) 2 2) DegreeOneMiddleResidualSpectrum329.graph sourceMap0156=true := by decide +kernel
theorem fusedMap0156_checked : acceptsGraphIso
    (fused (graph core0156) (root 8) 2 2) DegreeTwoThreeSpectrum2842.graph fusedMap0156=true := by decide +kernel
theorem certified0156 : Certified (graph core0156) (root 8) 2 2 :=
  of_native_maps core0156 DegreeOneMiddleResidualSpectrum329.graph DegreeTwoThreeSpectrum2842.graph
    sourceMap0156 fusedMap0156 sourceMap0156_checked fusedMap0156_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0156
#print axioms sourceMap0156_checked
#print axioms fusedMap0156_checked
#print axioms certified0156
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
