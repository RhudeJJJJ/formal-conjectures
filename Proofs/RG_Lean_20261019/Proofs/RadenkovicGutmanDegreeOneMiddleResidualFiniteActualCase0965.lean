/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0965 : Family 10 := level10.get ⟨805,by decide⟩
def sourceMap0965 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0965 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0965_checked : acceptsGraphIso
    (source (graph core0965) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2253.graph sourceMap0965=true := by decide +kernel
theorem fusedMap0965_checked : acceptsGraphIso
    (fused (graph core0965) (root 10) 2 2) DegreeTwoThreeSpectrum5602.graph fusedMap0965=true := by decide +kernel
theorem certified0965 : Certified (graph core0965) (root 10) 2 2 :=
  of_native_maps core0965 DegreeOneMiddleResidualSpectrum2253.graph DegreeTwoThreeSpectrum5602.graph
    sourceMap0965 fusedMap0965 sourceMap0965_checked fusedMap0965_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0965
#print axioms sourceMap0965_checked
#print axioms fusedMap0965_checked
#print axioms certified0965
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
