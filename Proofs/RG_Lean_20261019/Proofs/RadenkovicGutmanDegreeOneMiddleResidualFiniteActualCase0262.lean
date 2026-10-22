/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0262 : Family 9 := level9.get ⟨82,by decide⟩
def sourceMap0262 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0262 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0262_checked : acceptsGraphIso
    (source (graph core0262) (root 9) 2 2) DegreeOneMiddleResidualSpectrum678.graph sourceMap0262=true := by decide +kernel
theorem fusedMap0262_checked : acceptsGraphIso
    (fused (graph core0262) (root 9) 2 2) DegreeTwoThreeSpectrum4033.graph fusedMap0262=true := by decide +kernel
theorem certified0262 : Certified (graph core0262) (root 9) 2 2 :=
  of_native_maps core0262 DegreeOneMiddleResidualSpectrum678.graph DegreeTwoThreeSpectrum4033.graph
    sourceMap0262 fusedMap0262 sourceMap0262_checked fusedMap0262_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0262
#print axioms sourceMap0262_checked
#print axioms fusedMap0262_checked
#print axioms certified0262
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
