/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0702 : Family 10 := level10.get ⟨310,by decide⟩
def sourceMap0702 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0702 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0702_checked : acceptsGraphIso
    (source (graph core0702) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1771.graph sourceMap0702=true := by decide +kernel
theorem fusedMap0702_checked : acceptsGraphIso
    (fused (graph core0702) (root 10) 2 2) DegreeTwoThreeSpectrum5507.graph fusedMap0702=true := by decide +kernel
theorem certified0702 : Certified (graph core0702) (root 10) 2 2 :=
  of_native_maps core0702 DegreeOneMiddleResidualSpectrum1771.graph DegreeTwoThreeSpectrum5507.graph
    sourceMap0702 fusedMap0702 sourceMap0702_checked fusedMap0702_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0702
#print axioms sourceMap0702_checked
#print axioms fusedMap0702_checked
#print axioms certified0702
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
