/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0342 : Family 9 := level9.get ⟨217,by decide⟩
def sourceMap0342 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0342 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0342_checked : acceptsGraphIso
    (source (graph core0342) (root 9) 2 2) DegreeOneMiddleResidualSpectrum845.graph sourceMap0342=true := by decide +kernel
theorem fusedMap0342_checked : acceptsGraphIso
    (fused (graph core0342) (root 9) 2 2) DegreeTwoThreeSpectrum4004.graph fusedMap0342=true := by decide +kernel
theorem certified0342 : Certified (graph core0342) (root 9) 2 2 :=
  of_native_maps core0342 DegreeOneMiddleResidualSpectrum845.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap0342 fusedMap0342 sourceMap0342_checked fusedMap0342_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0342
#print axioms sourceMap0342_checked
#print axioms fusedMap0342_checked
#print axioms certified0342
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
