/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0284 : Family 9 := level9.get ⟨115,by decide⟩
def sourceMap0284 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0284 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0284_checked : acceptsGraphIso
    (source (graph core0284) (root 9) 2 2) DegreeOneMiddleResidualSpectrum704.graph sourceMap0284=true := by decide +kernel
theorem fusedMap0284_checked : acceptsGraphIso
    (fused (graph core0284) (root 9) 2 2) DegreeTwoThreeSpectrum4130.graph fusedMap0284=true := by decide +kernel
theorem certified0284 : Certified (graph core0284) (root 9) 2 2 :=
  of_native_maps core0284 DegreeOneMiddleResidualSpectrum704.graph DegreeTwoThreeSpectrum4130.graph
    sourceMap0284 fusedMap0284 sourceMap0284_checked fusedMap0284_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0284
#print axioms sourceMap0284_checked
#print axioms fusedMap0284_checked
#print axioms certified0284
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
