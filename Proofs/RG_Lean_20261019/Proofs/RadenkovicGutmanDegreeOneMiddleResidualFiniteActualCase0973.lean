/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0973 : Family 10 := level10.get ⟨834,by decide⟩
def sourceMap0973 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0973 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0973_checked : acceptsGraphIso
    (source (graph core0973) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2265.graph sourceMap0973=true := by decide +kernel
theorem fusedMap0973_checked : acceptsGraphIso
    (fused (graph core0973) (root 10) 2 2) DegreeTwoThreeSpectrum5662.graph fusedMap0973=true := by decide +kernel
theorem certified0973 : Certified (graph core0973) (root 10) 2 2 :=
  of_native_maps core0973 DegreeOneMiddleResidualSpectrum2265.graph DegreeTwoThreeSpectrum5662.graph
    sourceMap0973 fusedMap0973 sourceMap0973_checked fusedMap0973_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0973
#print axioms sourceMap0973_checked
#print axioms fusedMap0973_checked
#print axioms certified0973
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
